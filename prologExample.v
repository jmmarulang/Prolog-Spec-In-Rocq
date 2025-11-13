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

Notation R := WindControllerSpec.R.
Notation state := SafetyProof.state.

(*
We model the probability of a car colliding with an obstacle on finalState os. 
To calculate probabilities, we model Problog using dependent types

The equivalent Problog code is:

1::start(car,clear); 0::start(car,coli).
0.7::trans(car,T,clear,clear); 0.3::trans(car,T,clear,coli).
0.2::trans(car,T,coli,clear); 0.8::trans(car,T,coli,coli).

state(A,0,S) :- start(A,S).
state(A,T,S) :- T > 0, TT is T-1, state(A,TT,clear), trans(A,TT,clear,S).
state(A,T,S) :- T > 0, TT is T-1, state(A,TT,coli), trans(A,TT,coli,S).
*)

(*
Collision state of the car.
The car is either safe or has collided
*)
  Inductive CState : Type := 
| safe: CState 
| coll: CState.

(*
Probability of the car there being a collision at the start.
We set this probability to 0
*)
Inductive Start : CState -> R -> Prop := 
| start_s : Start safe (1)%R
| start_c : Start coll (0)%R.

(*
Transition probabilities between safe and collision states.
Note we say there is a chance the car keeps moving after a collision.
*)
Inductive Trans: CState -> CState -> R -> Prop := 
| trans_s_s: Trans safe safe (7/10)%R
| trans_s_c: Trans safe coll (3/10)%R
| trans_c_s: Trans coll safe (2/10)%R
| trans_c_c: Trans coll coll (8/10)%R.

(*
The system model.
ASSUMING THE EVENTS ARE INDEPENDENT. 
The model starts in the initial state.
If the car is on the road on state s and:
- the probability of it being safe is p1
- the transition probability from safe into cs is p2
- the probability of it having collided is p3 and
- the transition probability from collision into cs is p2
then the probability of the car moving into state cs is (p1 * p2) + (p3 * p4)
*)
Inductive GState: state -> CState -> R -> Prop :=
| gstate_0 : forall {p} cs, Start cs p -> 
  GState initialState cs p
| gstate_st : forall {p1} {p2} {p3} {p4} {o} s cs, 
  onRoad s -> GState s safe p1 -> Trans safe cs p2 ->
  GState s coll p3 -> Trans coll cs p4 -> 
  GState (nextState o s) cs ((p1 * p2) + (p3 * p4))%R.

(*Useful lemma for proofs*)
Lemma is_state_st : forall {p p1 p2 p3 p4: R} {o} s cs, 
        (p = p1 * p2 + p3 * p4)%R ->  onRoad s ->
        GState s safe p1 -> Trans safe cs p2 -> GState s coll p3 ->
        Trans coll cs p4 -> GState (nextState o s) cs p.
Proof. by do 8 move=> ?; move=> ->; apply gstate_st. Qed. 

(*Proof that the probability of the car being safe at the start is 1*)
Goal (GState initialState safe 1%R).
Proof. apply /gstate_0; first by econstructor. Qed.

(*Proof that the probability of the car being safe on the second state is 0.7*)
Goal (forall o, GState (nextState o initialState) safe (7/10)%R).
Proof.
    move=> ?; apply /is_state_st; try econstructor; last first.
    all: try exact initialState_onRoad. 
    exact start_c. 
    exact start_s.
    by nra.
Qed.

(*Proof that the probability of the car being safe on the third state is 0.55*)
Goal (forall (o1 o2 : observation), 
  (forall x, List.In x [:: o1; o2] -> validObservation x) -> 
  GState (finalState [:: o1; o2]) safe (55/100)%R).
Proof.
    move=> o1 o2 H. 
    have := finalState_onRoad [:: o2]; rewrite /finalState=> //= fonR.
    apply /is_state_st; repeat econstructor; last first.
    all: try exact initialState_onRoad.
    by apply /fonR=> x []//<-; apply H; right; left.
    by nra.
Qed.

(*
We compare our encoding of Problog using dependent types with a regular 
recursive function that calculates probabilities.
Perhaps this could be interpreted as verifying the correctess of the model?
*)
Definition start_prob (cs : CState) : R := 
match cs with 
| safe => 1
| coll => 0
end.

Definition trans_prob (cs : CState) (new_cs : CState) : R := 
match cs, new_cs with 
| safe, safe=> (7/10)%R
| safe, coll=> (3/10)%R
| coll, safe=> (2/10)%R
| coll, coll=> (8/10)%R
end.

Fixpoint final_prob (ss : seq.seq observation) (cs : CState) : R := 
match ss with 
| [:: ] => start_prob cs
| s :: ss => (final_prob ss safe)*(trans_prob safe cs) + 
  (final_prob ss coll)*(trans_prob coll cs)
end.

(*
Proof that the type theoretic encoding and the recursive function match
for any timestep*)
Lemma gstate_is_final_prob:  (forall os cs, 
  (forall o, List.In o os -> validObservation o) -> 
  GState (finalState os) cs (final_prob os cs)%R).
Proof.
  elim=>[[]|o os IH [o_valid|o_valid]]//=; repeat econstructor.
  1,4: by apply finalState_onRoad=> ? ?; apply /o_valid /in_cons.
  all:by apply IH=> ? ?; apply /o_valid /in_cons.
Qed.


    