import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.OnlineHistoryCost

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

noncomputable def initialWeightPolynomial : Polynomial ℕ := 2*X+3+statePolynomial
lemma initial_weight {G : GraphInput} [Nontrivial (Fin G.n)] (f : Edges→Edges) (p : Trial.Parameters G) :
    weight (initial f p) ≤ initialWeightPolynomial.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  have hs:=history_size f p p.K (initial f p).2 (history_initial f p)
  have hw:=weight_le_stateSize (initial f p).2
  have hk:=(sizeNorm_fields p (graph f (ExecutableAdaptive.graphRep G))).2.1
  rw [weight_prod]
  have hl : weight (initial f p).1=2*p.K+1 := by simp only [initial,weight_replicate,show weight false=1 from rfl];omega
  rw [hl]
  simp only [initialWeightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  omega
end MatchingFPRAS.OnlineTrial

namespace MatchingFPRAS.OnlineGuard
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineTrial

lemma trial_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (f : Edges→Edges) (_hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G),
    trialRealizer.cost (OnlineTrial.initial f p)+(trial (OnlineTrial.initial f p)).worst weight≤
      q.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  obtain ⟨q,hq⟩:=sweep_bound
  obtain ⟨r,hr⟩:=work_checked
  refine ⟨q+2*(r.comp statePolynomial),?_⟩
  intro G inst f hf p
  let n:=sizeNorm p (graph f (ExecutableAdaptive.graphRep G))
  have hs:=hq G f hf p
  have hb : (sweep (OnlineTrial.initial f p)).All (fun s=>checkedRealizer.cost s+(checked s).worst weight≤r.eval (statePolynomial.eval n)) :=
    (sweep_history f hf p).mono (fun s hs=>(hr s).trans (polynomial_eval_monotone r (history_size f p 0 s hs)))
  have h1:=Experiment.worst_le _ _ _ (hb.mono (fun s hs=>Nat.le_trans (Nat.le_add_right _ _) hs))
  have h2:=Experiment.worst_le _ _ _ (hb.mono (fun s hs=>Nat.le_trans (Nat.le_add_left _ _) hs))
  change sweepRealizer.cost _+(sweep _).worst checkedRealizer.cost+((sweep _).bind checked).worst weight≤_
  rw [Experiment.worst_bind]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  dsimp only [n] at *
  omega
end MatchingFPRAS.OnlineGuard

namespace MatchingFPRAS.OnlineAmplification
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineTrial OnlineSample

lemma run_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (f : Edges→Edges) (_hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G) (r : ℕ),
    runRealizer.cost (r,OnlineTrial.initial f p)+(run (r,OnlineTrial.initial f p)).worst weight≤
      q.eval (r+sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  obtain ⟨q,hq⟩:=OnlineGuard.trial_bound
  obtain ⟨s,hs⟩:=OnlineTree.traverse_bound OnlineGuard.trialRealizer
  obtain ⟨u,hu⟩:=work_repeatInput (A:=TrialInput)
  obtain ⟨v,hv⟩:=OnlineMedian.polynomial_median
  let I := initialWeightPolynomial
  let R : Polynomial ℕ := 5*X+2+I
  let B : Polynomial ℕ := X*(I+1)+1+q
  let T := u.comp R+s.comp B
  refine ⟨T+2*(v.comp T),?_⟩
  intro G inst f hf p r
  let n:=sizeNorm p (graph f (ExecutableAdaptive.graphRep G))
  let z:=r+n
  let x : TrialInput:=OnlineTrial.initial f p
  have hn:n≤z := by dsimp [z];omega
  have hr:r≤z := by dsimp [z];omega
  have hx : weight x≤I.eval z := (initial_weight f p).trans (polynomial_eval_monotone I hn)
  have hinput : r+weight (r,x) ≤R.eval z := by
    have hw:=weight_nat_numeric r
    simp only [weight_prod,R,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
    omega
  have hrep := (hu (r,x)).trans (polynomial_eval_monotone u hinput)
  have hwrep : weight (List.replicate r x)≤B.eval z := by
    rw [weight_replicate]
    simp only [B,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith
  have ht : ∀ a∈List.replicate r x,OnlineGuard.trialRealizer.cost a+(OnlineGuard.trial a).worst weight≤B.eval z := by
    intro a ha
    have he: a=x := (List.mem_replicate.mp ha).2
    rw [he]
    exact ((hq G f hf p).trans (polynomial_eval_monotone q hn)).trans (by
      simp only [B,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one];omega)
  have htrav:=hs (List.replicate r x) (B.eval z) hwrep ht
  have htrial : trialsRealizer.cost (r,x)+(trials (r,x)).worst weight≤T.eval z := by
    change repeatInputRealizer.cost (r,x)+(OnlineTree.traverse OnlineGuard.trialRealizer).cost (List.replicate r x)+
      (OnlineTree.traverseM OnlineGuard.trial (List.replicate r x)).worst weight≤_
    simp only [T,Polynomial.eval_add,Polynomial.eval_comp]
    change repeatInputRealizer.cost (r,x)+weight (List.replicate r x)≤u.eval (R.eval z) at hrep
    omega
  have htail : (trials (r,x)).worst (fun as=>OnlineMedian.medianRealizer.cost as+weight (OnlineMedian.median as))≤v.eval (T.eval z) := by
    apply Experiment.worst_le _ _ _
    exact (Experiment.all_worst (trials (r,x)) weight).mono (fun as hw=>(hv as).trans
      (polynomial_eval_monotone v (hw.trans (by omega))))
  have hcost : (trials (r,x)).worst OnlineMedian.medianRealizer.cost≤v.eval (T.eval z) :=
    (Experiment.worst_mono _ _ _ ((Experiment.all_true _).mono (fun _ _=>Nat.le_add_right _ _))).trans htail
  have hout : (trials (r,x)).worst (weight ∘ OnlineMedian.median)≤v.eval (T.eval z) :=
    (Experiment.worst_mono _ _ _ ((Experiment.all_true _).mono (fun _ _=>Nat.le_add_left _ _))).trans htail

  have hboth : (trials (r,x)).worst OnlineMedian.medianRealizer.cost+
      (trials (r,x)).worst (weight ∘ OnlineMedian.median)≤2*v.eval (T.eval z) := by omega

  clear hcost hout htail
  change trialsRealizer.cost (r,x)+(trials (r,x)).worst OnlineMedian.medianRealizer.cost+
    (run (r,x)).worst weight≤_
  rw [run,Experiment.worst_map]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  change _ ≤ T.eval z+2*v.eval (T.eval z)
  omega
end MatchingFPRAS.OnlineAmplification

end OAI
