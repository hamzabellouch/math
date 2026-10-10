import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineHistorySize

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
lemma all_of_qaverage {A B : Type} [Fintype B] [Nonempty B] (p : Experiment A) (f : B→A)
    (hm : ∀ h,p.mean h=qaverage (h ∘ f)) (P : A→Prop) (hf : ∀ b,P (f b)) : p.All P := by
  classical
  rw [all_indicator,hm]
  calc
    _=qaverage (fun _ : B=>(0:ℚ)) := by
      apply qaverage_congr
      intro b
      simp only [Function.comp_apply,ite_eq_left (hf b)]
    _=0 := qaverage_const 0
end MatchingFPRAS.PhysicalStream.Experiment

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable def initial (f : Edges→Edges) (p : Trial.Parameters G) : List Bool×State :=
  (List.replicate p.K false,state f (represent p (FiniteTrial.firstLayer p) PUnit.unit))
def History (f : Edges→Edges) (p : Trial.Parameters G) (k : ℕ) (s : State) : Prop :=
  ∃ (j : ℕ) (hj : j≤p.K) (x : (FiniteTrial.layers p j hj).Ω),j+k=p.K ∧
    s=state f (represent p (FiniteTrial.layers p j hj) x)
lemma history_initial (f : Edges→Edges) (p : Trial.Parameters G) : History f p p.K (initial f p).2 := by
  exact ⟨0,by omega,PUnit.unit,by omega,rfl⟩
lemma history_size (f : Edges→Edges) (p : Trial.Parameters G) (k : ℕ) (s : State)
    (hs : History f p k s) : stateSize s≤ statePolynomial.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  obtain ⟨j,hj,x,_,rfl⟩:=hs
  exact state_weight_bound f p j hj x
lemma history_step (f : Edges→Edges) (hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G)
    (k : ℕ) (s : State) (hs : History f p (k+1) s) : (step s).All (History f p k) := by
  classical
  obtain ⟨j,hj,x,hjk,rfl⟩:=hs
  apply Experiment.all_of_qaverage _
    (fun b=>state f (represent p ((FiniteTrial.layers p j hj).append p hj)
      ⟨x,((FiniteTrial.layers p j hj).state x).drawStage p hj b⟩))
  · intro h
    rw [OnlineGraph.step_mean f hf,step_mean p hj]
    rfl
  · intro b
    exact ⟨j+1,by omega,⟨x,((FiniteTrial.layers p j hj).state x).drawStage p hj b⟩,by omega,rfl⟩
lemma sweep_history (f : Edges→Edges) (hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G) :
    (sweep (initial f p)).All (History f p 0) := by
  have hall : ∀ as : List Bool,∀ s,History f p as.length s→
      (OnlineTree.foldM body as s).All (History f p 0) := by
    intro as
    induction as with
    | nil => intro s hs;exact hs
    | cons a as ih =>
      intro s hs
      rw [OnlineTree.foldM,Experiment.all_bind]
      exact (history_step f hf p as.length s hs).mono (fun v hv=>ih v hv)
  exact hall _ _ (by simpa only [initial,List.length_replicate] using history_initial f p)

open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

lemma sweep_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (f : Edges→Edges) (_hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G),
    sweepRealizer.cost (initial f p)+(sweep (initial f p)).worst weight≤
      q.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  obtain ⟨q,hq⟩:=work_body
  let C := q.comp (2*statePolynomial+2)
  let M : Polynomial ℕ := 2*X+1
  refine ⟨X*(C+14*M+34)+10+statePolynomial,?_⟩
  intro G inst f hf p
  let n:=sizeNorm p (graph f (ExecutableAdaptive.graphRep G))
  have hk : p.K ≤ n := (sizeNorm_fields p _).2.1
  have hw : weight (initial f p).1≤M.eval n := by
    simp only [initial,weight_replicate,show weight false=1 from rfl,M,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hc : ∀ a∈(initial f p).1,∀ k<(initial f p).1.length,∀ s,History f p (k+1) s→
      bodyRealizer.cost (a,s)≤C.eval n := by
    intro a ha k hk s hs
    have hsz : stateSize s ≤ statePolynomial.eval n := history_size f p (k+1) s hs
    have hw:=weight_le_stateSize s
    have hb:=hq (a,s)
    have ha' : weight a=1 := by
      have he : a=false := (List.mem_replicate.mp ha).2
      rw [he];rfl
    simp only [weight_prod,ha'] at hb
    have hm : stateSize s+(1+1+weight s)≤(2*statePolynomial+2).eval n := by
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
      omega
    exact (Nat.le_add_right _ _).trans (hb.trans (by simpa only [C,Polynomial.eval_comp] using polynomial_eval_monotone q hm))
  have hh:=OnlineTree.fold_cost_bound body bodyRealizer.cost (initial f p).1 (initial f p).2
    (History f p) (C.eval n) (M.eval n)
    (by simpa only [initial,List.length_replicate] using history_initial f p) hw
    (fun a ha k hk s hs=>history_step f hf p k s hs) hc
  have hout : (sweep (initial f p)).worst weight≤ statePolynomial.eval n := by
    apply Experiment.worst_le _ _ _
    exact hh.2.mono (fun s hs=>(weight_le_stateSize s).trans (history_size f p 0 s hs))
  have hmul:=Nat.mul_le_mul_right (C.eval n+14*M.eval n+34) hk
  change OnlineTree.Fold.cost body bodyRealizer.cost (initial f p).1 (initial f p).2+_≤_
  have hlen : (initial f p).1.length=p.K := List.length_replicate
  rw [hlen] at hh
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change _ ≤ n*(C.eval n+14*M.eval n+34)+10+statePolynomial.eval n
  omega
end MatchingFPRAS.OnlineTrial

end OAI
