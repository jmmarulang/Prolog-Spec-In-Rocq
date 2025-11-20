From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
From mathcomp Require Import ssralg poly ssrnum ssrint interval archimedean finmap.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import sequences derive esum measure exp trigo realfun.
From mathcomp Require Import numfun lebesgue_measure lebesgue_integral kernel.
From mathcomp Require Import lra seq.
Require Import Coq.Lists.List.
From mathcomp Require Import classical_sets reals ereal.
From mathcomp Require Import normedtype real_interval.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Local Open Scope seq_scope.

Require Import WindControllerSpec.
Require Import SafetyProof.

(*Notation R := WindControllerSpec.R.*)
Notation state := SafetyProof.state.
Notation maxWindShift := SafetyProof.maxWindShift.
Notation maxSensorError := SafetyProof.maxSensorError.

Section inside_invariant.
(*
%% The system is inside the invariant if the current observation is valid and
%% we were in the invariant in the previous step and 
%% the controller behaves correctly.

0.9::startIn(inside); 0.2::startIn(outside).
0.7::validInput(wind,T).
0.8::validInput(sensor,T).
observationValid(T) :- validInput(wind,T), validInput(sensor,T).

state(0) :- startIn(inside).
state(T) :- T > 0, TT is T-1, observationValid(T), state(TT).

query(state(5)).
*)

Context {R: realType}.

Inductive Instate: Type := inside | outside.

Inductive InStart: Instate -> R -> Type := 
| start_in: InStart inside (9/10)%R
| start_out: InStart outside (1/10)%R. 

Inductive Input: Type := wind | sensor. 

Inductive ValidInput: state -> Input -> R -> Type :=
| vwind {s}: ValidInput s wind (7/10)%R
| vsensor {s}: ValidInput s sensor (8/10)%R.

Inductive ValidObsevation: state -> R -> Type :=
| vo {s p1 p2}: ValidInput s wind p1 -> ValidInput s sensor p2 -> 
  ValidObsevation s (p1 * p2)%R. 

Definition SafeController := forall x y,
  `|x| <= roadWidth + maxSensorError ->
  `|y| <= roadWidth + maxSensorError ->
  `|controller x y + 2 * x - y| < roadWidth - maxWindShift - 3 * maxSensorError.

Inductive Inside: state -> R -> Prop :=
| Inside_0: forall {p}, InStart inside p -> Inside initialState p
| Inside_st: forall {p1 p2} s o, ValidObsevation (nextState o s) p1 -> 
  Inside s p2 -> SafeController -> Inside (nextState o s) (p1 * p2)%R.

(*Useful lemma for proofs*)
Lemma is_state_st : forall {p1 p2 p} s o, ValidObsevation (nextState o s) p1 -> 
  Inside s p2 -> SafeController -> (p = p1 * p2) -> Inside (nextState o s) p.
Proof. by (do 8 move=> ?)=> ->; apply /Inside_st. Qed.

Goal (Inside initialState (9/10)%R).
Proof. apply /Inside_0; first by econstructor. Qed.

Goal (forall o, Inside (nextState o initialState) (63/125)%R).
Proof.
move=> ?; apply/is_state_st; repeat econstructor; nra + exact /controller_lem.
Qed.

Definition start_prob (inst : Instate) : R := 
match inst with 
| inside => (9/10)%R
| outside => (1/10)%R
end.

Definition vinput_prob (input : Input) : R := 
match input with 
| wind => (7/10)%R
| sensor => (8/10)%R
end.

Definition vobs_prob : R := (vinput_prob wind) * (vinput_prob sensor).

Fixpoint inside_prob (os : seq.seq observation) : R := 
match os with 
| [:: ] => start_prob inside
| o :: os => (vobs_prob) * (inside_prob os)
end.

Lemma inside_is_inside_prob: forall os, Inside (finalState os) (inside_prob os).
Proof.
  elim=>[|o os IH]/=; repeat econstructor; exact controller_lem + exact IH.
Qed.

End inside_invariant.

(*
Context {R: realType}.

Inductive InStart: R -> Prop := 
| start_in: InStart (9/10)%R
| start_out: InStart (1/10)%R. 

Inductive Input: Type :=
| wind: Input
| sensor: Input.

Inductive ValidInput : state -> Input -> R -> Type :=
| vw {s}: ValidInput s wind (7/10)%R
| vs {s}: ValidInput s sensor (8/10)%R.

Inductive ValidObsevation: forall {i1 i2 p1 p2} s, 
  ValidInput s i1 p1 -> ValidInput s i2 p2 -> Type :=
| vo {s}: ValidObsevation s vw vs.

Inductive Inside: state -> R -> Prop :=
| Inside_0: forall {p}, InStart p -> Inside initialState p
| Inside_st: forall s, forall {p1 p2 p3 i1 i2 o} {vi1 : ValidInput _ i1 p1} 
  {vi2 : ValidInput _ i2 p2}, 
  ValidObsevation (nextState o s) vi1 vi2 -> Inside s p3 -> 
  Inside (nextState o s) (p1 * p2 * p3).

(*Useful lemma for proofs*)
Lemma is_state_st : forall s, forall {p p1 p2 p3 i1 i2 o} 
  {vi1 : ValidInput _ i1 p1} {vi2 : ValidInput _ i2 p2}, (p = p1 * p2 * p3) ->
  ValidObsevation (nextState o s) vi1 vi2 -> Inside s p3 -> Inside (nextState o s) p.
Proof. 
by (do 10 move=> ?)=> ->; apply /Inside_st. Qed.

Goal (Inside initialState (9/10)%R).
Proof. apply /Inside_0; first by econstructor. Qed.

Goal (forall o, Inside (nextState o initialState) (63/125)%R).
Proof. by move=> ?; apply /is_state_st; repeat econstructor; nra. Qed.

End inside_invariant.
*)