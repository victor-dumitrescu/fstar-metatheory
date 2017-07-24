(*
   Copyright 2014-2015
     Simon Forest - Inria and ENS Paris
     Catalin Hritcu - Inria
     Nikhil Swamy - Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module SystemF

open FStar.Constructive
open FStar.Classical
open FStar.FunctionalExtensionality
open FStar.StrongExcludedMiddle

(* Constructive-style progress and preservation proof for STLC with
   strong reduction, using deBruijn indices and parallel substitution. *)

type var = nat

type knd =
  | KTyp : knd

type typ =
  | TVar  : var -> typ
  | TArr  : typ -> typ -> typ
  | TUniv : typ -> typ 
(*  | TUnit : typ *)


type exp =
  | EVar    : var -> exp
  | EApp    : exp -> exp -> exp
  | ELam    : typ -> exp -> exp
(*  | EUnit   : exp *)
  | ETyLam  : exp -> exp
  | ETyApp  : exp -> typ -> exp

(* Parallel substitution operation `subst` *)

(* The termination argument uses a lexicographic ordering composed of:
   0) a bit saying whether the expression is a variable or not;
   1) an _undecidable_ well-founded order on substitutions that
      equates all renamings, equates all non-renamings, and makes
      renamings strictly smaller than non-renamings; we write down a
      non-constructive function is_renaming mapping substitutions
      (infinite objects) to 0 (renaming) or 1 (non-renaming)
   2) the structure of the expression e *)

type esub = var -> Tot exp
type tsub = var -> Tot typ

(* renamings replace variables with other variables *)
type erenaming (s:esub) = (forall (x:var). EVar? (s x))
type trenaming (s:tsub) = (forall (x:var). TVar? (s x))

val is_erenaming : s:esub -> GTot (n:int{  (erenaming s  ==> n=0) /\
                                       (~(erenaming s) ==> n=1)})
let is_erenaming s = (if strong_excluded_middle (erenaming s) then 0 else 1)

val is_trenaming : s:tsub -> GTot (n:int{  (trenaming s  ==> n=0) /\
                                       (~(trenaming s) ==> n=1)})
let is_trenaming s = (if strong_excluded_middle (trenaming s) then 0 else 1)

val esub_inc : var -> Tot exp
let esub_inc y = EVar (y+1)

val tsub_inc : var -> Tot typ 
let tsub_inc y = TVar (y+1)

val erenaming_sub_inc : unit -> Lemma (erenaming (esub_inc))
let erenaming_sub_inc _ = ()

val trenaming_sub_inc : unit -> Lemma (trenaming (tsub_inc))
let trenaming_sub_inc _ = ()

let is_evar (e:exp) : int = if EVar? e then 0 else 1
let is_tvar (t:typ) : int = if TVar? t then 0 else 1

(* substituting types in types *)
val tsubst: s:tsub -> t:typ -> Pure typ (requires True)
    (ensures (fun t' -> (trenaming s /\ TVar? t) ==> TVar? t'))
    (decreases %[is_tvar t; is_trenaming s; t])
let rec tsubst s t =
  match t with
  | TVar x -> s x
  | TArr t1 t2 -> TArr (tsubst s t1) (tsubst s t2)
  | TUniv t1 -> 
     let sub_tlam : y:var -> Tot (t:typ{trenaming s ==> TVar? t}) = 
       fun y -> if y=0  then TVar y
                     else (tsubst tsub_inc (s (y - 1))) in
     TUniv (tsubst sub_tlam t1)
  (* | TUnit -> TUnit *)

(* substituting types in expressions *)
val esubst_t : s:tsub -> e:exp -> Tot exp
let rec esubst_t s e =
  match e with
    | EVar _ -> e
    | EApp e1 e2 -> EApp (esubst_t s e1) (esubst_t s e2)
    | ELam t e1 -> ELam (tsubst s t) (esubst_t s e1)
    (* | EUnit -> EUnit *)
    | ETyLam e -> 
        let esub_tylam : ty:var -> Tot typ = fun y ->
	      if y = 0 then TVar y
	               else tsubst tsub_inc (s (y - 1))
      in
      ETyLam (esubst_t esub_tylam e)
    | ETyApp e1 t -> ETyApp (esubst_t s e1) (tsubst s t)

(*
val esub_tylam : s:esub -> Tot typ
let esub_tylam s y = if y = 0 then TVar y
	                 else tsubst tsub_inc (s (y - 1))
*)

(* substituting expressions in expressions *)
val esubst : s:esub -> e:exp -> Pure exp (requires True)
     (ensures (fun e' -> (erenaming s /\ EVar? e) ==> EVar? e'))
     (decreases %[is_evar e; is_erenaming s; e])
let rec esubst s e =
  match e with
  | EVar x -> s x
  | ELam t e1 ->
     let sub_elam : y:var -> Tot (e:exp{erenaming s ==> EVar? e}) =
       fun y -> if y=0 then EVar y
                    else esubst esub_inc (s (y-1))            (* shift +1 *)
     in ELam t (esubst sub_elam e1)
  (* | EUnit -> EUnit *)
  | EApp e1 e2 -> EApp (esubst s e1) (esubst s e2)
  | ETyLam e1 -> ETyLam (esubst (fun y -> esubst_t tsub_inc (s y)) e1)
  | ETyApp e1 t1 -> ETyApp (esubst s e1) t1

val sub_elam: s:esub -> Tot esub
let sub_elam s y = if y=0 then EVar y
                   else esubst esub_inc (s (y-1))

val esub_beta : exp -> Tot esub
let esub_beta v = fun y -> if y = 0 then v      (* substitute *)
                           else (EVar (y-1))    (* shift -1 *)

val tsub_beta: typ -> Tot tsub
let tsub_beta v = fun y -> if y = 0 then v
                           else (TVar (y-1))


(* 
(* substitution on types *)
type tsub = var -> Tot typ

type trenaming (s:tsub) = (forall (x:var). TVar? (s x))

val is_trenaming : s:tsub -> GTot (n:int{  (trenaming s  ==> n=0) /\
                                       (~(trenaming s) ==> n=1)})
let is_trenaming s = (if strong_excluded_middle (trenaming s) then 0 else 1)

val tsub_inc : var -> Tot typ
let tsub_inc y = TVar (y+1)

val trenaming_sub_inc : unit -> Lemma (trenaming (tsub_inc))
let trenaming_sub_inc _ = ()

let is_tvar (t:typ) : int = if TVar? t then 0 else 1

val tsubst : s:tsub -> t:typ -> Pure typ (requires True)
     (ensures (fun t' -> (trenaming s /\ TVar? t) ==> TVar? t'))
     (decreases %[is_tvar t; is_trenaming s; t])
let rec tsubst s t =
  match t with
  | TVar x -> s x
  | TLam t ->
     let sub_tlam : y:var -> Tot (t:typ{trenaming s ==> TVar? t}) =
       fun y -> if y=0 then TVar y
                       else tsubst tsub_inc (s (y-1))            (* shift +1 *)
     in TLam (tsubst sub_tlam t)
  | TApp t1 t2 -> TApp (tsubst s t1) (tsubst s t2)

val sub_elam: s:esub -> Tot esub
let sub_elam s y = if y=0 then EVar y
                   else esubst esub_inc (s (y-1))

val esub_beta : exp -> Tot esub
let esub_beta v = fun y -> if y = 0 then v      (* substitute *)
                           else (EVar (y-1))    (* shift -1 *)
*)

(* Small-step operational semantics; strong / full-beta reduction is
   non-deterministic, so necessarily as inductive relation *)

type step : exp -> exp -> Type =
  | SBeta : t:typ ->
            e1:exp ->
            e2:exp ->
            step (EApp (ELam t e1) e2) (esubst (esub_beta e2) e1)
  | SApp1 : #e1:exp ->
             e2:exp ->
            #e1':exp ->
            $hst:step e1 e1' ->
                 step (EApp e1 e2) (EApp e1' e2)
  | SApp2 :  e1:exp ->
            #e2:exp ->
            #e2':exp ->
            $hst:step e2 e2' ->
                 step (EApp e1 e2) (EApp e1 e2')
  | STyApp:  #e1:exp ->
              t:typ ->
             #e1':exp ->
             $hst:step e1 e1' ->
             step (ETyApp e1 t) (ETyApp e1' t)
  | STyBeta:  t:typ ->
              e1:exp ->
              step (ETyApp (ETyLam e1) t) (esubst_t (tsub_beta t) e1)

(* Typing environments *)
type t_env = var -> Tot (option knd)
type e_env = var -> Tot (option typ)

let empty_t: t_env = fun _ -> None
let empty_e: e_env = fun _ -> None

noeq type env =
  | MkEnv: t:t_env -> e:e_env -> env

val lookup_tvar: env -> nat -> Tot (option knd)
let lookup_tvar g n = MkEnv?.t g n

val lookup_evar: env -> nat -> Tot (option typ)
let lookup_evar g n = MkEnv?.e g n

val empty: env
let empty = MkEnv empty_t empty_e

(* val extend_tvar: g:env -> n:nat -> Tot env
let extend_tvar g n =
  let t_env = fun (t:nat) -> if t < n then lookup 

val extend_evar: typ -> e_env -> Tot e_env
let extend_evar t g y = if y = 0 then Some t
                   else g (y-1) *)

(* Type variables don't depend on expressions, so we can extend the environment for expressions
   independent of the one for type variables *)
val extend_evar: g:env -> t:typ -> Tot env
let extend_evar g t =
  let t_env = fun (x:var) -> lookup_tvar g x in
  let e_env = fun (x:var) -> if x = 0 then Some t else lookup_evar g (x-1) in
  MkEnv t_env e_env

(* When extending the environment for types, we need to also find and shift all the type variables 
   used in the types of expressions in e_env *)
val extend_tvar: g:env -> Tot env
let extend_tvar g =
  let t_env = fun (x:var) -> if x = 0 then Some KTyp else lookup_tvar g (x-1) in
  let e_env = fun (x:var) -> match lookup_evar g x with
    | None -> None
    | Some t -> Some (tsubst tsub_inc t) in
  MkEnv t_env e_env


(* Type system; as inductive relation *)
noeq type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
             x:var{Some? (lookup_evar g x)} ->
             typing g (EVar x) (Some?.v (lookup_evar g x))
  | TyLam : #g :env ->
             t :typ ->
            #e1:exp ->
            #t':typ ->
            $hbody:typing (extend_evar g t) e1 t' ->
                   typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:typ ->
            #t12:typ ->
            $h1:typing g e1 (TArr t11 t12) ->
            $h2:typing g e2 t11 ->
                typing g (EApp e1 e2) t12
  | TyTLam : #g:env ->
             #e:exp ->
             #t2:typ ->
             $hbody:typing (extend_tvar g) e t2 ->
                    typing g (ETyLam e) (TUniv t2)
  | TyTApp : #g:env ->
             #e1:exp ->
             #t12:typ ->
             #t2:typ ->
             $h1:typing g e1 (TUniv t12) ->
                 typing g (ETyApp e1 t2) (tsubst (tsub_beta t2) t12)
  (* | TyUnit : #g:env ->
             typing g EUnit TUnit *)

(* Progress *)

val is_value : exp -> Tot bool
let is_value e = ELam? e || ETyLam? e (* || EUnit? e *)

val progress : #e:exp -> #t:typ -> h:typing empty e t ->
                         Pure (cexists (fun e' -> step e e'))
                              (requires (~ (is_value e)))
                              (ensures (fun _ -> True)) (decreases h)
let rec progress #e #t h =
  match h with
  | TyApp #g #e1 #e2 #t11 #t12 h1 h2 ->
     (match e1 with
      | ELam t e1' -> ExIntro (esubst (esub_beta e2) e1') (SBeta t e1' e2)
      | _          -> let ExIntro e1' h1' = progress h1 in
                     ExIntro (EApp e1' e2) (SApp1 e2 h1'))
  | TyTApp #g #e1 #t12 #t2 h1 -> 
    (match e1 with
     | ETyLam e1' -> ExIntro (esubst_t (tsub_beta t2) e1') (STyBeta t2 e1')
     | _ -> let ExIntro e1' h1' = progress h1 in
           ExIntro (ETyApp e1' t2) (STyApp t2 h1'))

(* ### WIP: copied over from STLC *)

(* Substitution extensional - used by substitution lemma below *)
val subst_extensional: s1:sub -> s2:sub{feq s1 s2} -> e:exp ->
                       Lemma (requires True)
                             (ensures (subst s1 e = subst s2 e))
                             [SMTPat (subst s1 e); SMTPat (subst s2 e)]
let subst_extensional s1 s2 e = ()

(* Typing of substitutions (very easy, actually) *)
type subst_typing (s:sub) (g1:env) (g2:env) =
  (x:var{Some? (g1 x)} -> Tot(typing g2 (s x) (Some?.v (g1 x))))

(* Substitution preserves typing
   Strongest possible statement; suggested by Steven Schäfer *)
val substitution :
      #g1:env -> #e:exp -> #t:typ -> s:sub -> #g2:env ->
      h1:typing g1 e t ->
      hs:subst_typing s g1 g2 ->
      Tot (typing g2 (subst s e) t)
      (decreases %[is_var e; is_renaming s; e])
let rec substitution #g1 #e #t s #g2 h1 hs =
  match h1 with
  | TyVar x -> hs x
  | TyApp hfun harg -> TyApp (substitution s hfun hs) (substitution s harg hs)
  | TyLam tlam hbody ->
     let hs'' : subst_typing (sub_inc) g2 (extend tlam g2) =
       fun x -> TyVar (x+1) in
     let hs' : subst_typing (sub_elam s) (extend tlam g1) (extend tlam g2) =
       fun y -> if y = 0 then TyVar y
             else let n:var = y - 1 in //Silly limitation of implicits and refinements
                  substitution #_ #_ #(Some?.v (g1 n)) sub_inc #_ (hs n) hs'' //NS: needed to instantiate the Some?.v 
     in TyLam tlam (substitution (sub_elam s) hbody hs')
  | TyUnit -> TyUnit

(* Substitution for beta reduction
   Now just a special case of substitution lemma *)
val substitution_beta :
      #e:exp -> #v:exp -> #t_x:typ -> #t:typ -> #g:env ->
      h1:typing g v t_x ->
      h2:typing (extend t_x g) e t ->
      Tot (typing g (subst (sub_beta v) e) t) (decreases e)
let rec substitution_beta #e #v #t_x #t #g h1 h2 =
  let hs : subst_typing (sub_beta v) (extend t_x g) g =
    fun y -> if y = 0 then h1 else TyVar (y-1) in
  substitution (sub_beta v) h2 hs

(* Type preservation *)
val preservation : #e:exp -> #e':exp -> #g:env -> #t:typ ->
       ht:(typing g e t) ->
       hs:step e e' ->
       Tot (typing g e' t) (decreases ht)
let rec preservation #e #e' #g #t ht hs =
  let TyApp h1 h2 = ht in
  match hs with
  | SBeta tx e1' e2' -> substitution_beta #e1' #_ #_ #t #_ h2 (TyLam?.hbody h1)
  | SApp1 e2' hs1   -> TyApp (preservation h1 hs1) h2
  | SApp2 e1' hs2   -> TyApp h1 (preservation h2 hs2)
