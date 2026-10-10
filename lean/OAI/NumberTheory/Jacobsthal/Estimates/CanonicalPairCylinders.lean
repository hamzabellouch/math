import OAI.NumberTheory.Jacobsthal.Probability.CanonicalPairHitEvents

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

noncomputable def pairSurvivingHistory (a n : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawHistory (a+2*n)) :=
  (rawExtension a (a+2*n)).restrict (noPairHits_measurable a n (a+2*n) le_rfl v H)

noncomputable def pairStoppedHistory (a n : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawHistory (a+2*n+1)) :=
  (rawExtension a (a+2*n+1)).restrict (firstPairHitEvent_measurable a n (a+2*n+1) le_rfl v H)

instance pairSurvivingHistory_isFiniteKernel (a n : ℕ) (v H : ℝ) : IsFiniteKernel (pairSurvivingHistory a n v H) := by
  unfold pairSurvivingHistory
  infer_instance

instance pairStoppedHistory_isFiniteKernel (a n : ℕ) (v H : ℝ) : IsFiniteKernel (pairStoppedHistory a n v H) := by
  unfold pairStoppedHistory
  infer_instance

lemma pairSurvivingHistory_zero (a : ℕ) (v H : ℝ) : pairSurvivingHistory a 0 v H=Kernel.id := by
  ext h S hS
  rw [pairSurvivingHistory,Kernel.restrict_apply' _ _ _ hS,noPairHits_zero,inter_univ]
  simp only [Nat.mul_zero,Nat.add_zero,rawExtension,Kernel.partialTraj_self]

lemma pairStoppedHistory_zero (a : ℕ) (v H : ℝ) :
    pairStoppedHistory a 0 v H=(rawExtension a (a+1)).restrict
      (pairHitTest_measurable a 0 (a+1) (by omega) v H) := by
  ext h S hS
  rw [pairStoppedHistory,Kernel.restrict_apply' _ _ _ hS,Kernel.restrict_apply' _ _ _ hS,
    firstPairHitEvent,noPairHits_zero,univ_inter]

theorem pairSurvivingHistory_succ (a n : ℕ) (v H : ℝ) :
    pairSurvivingHistory a (n+1) v H=
      ((rawExtension (a+2*n) (a+2*(n+1))).restrict
        (pairHitTest_measurable a n (a+2*(n+1)) (by omega) v H).compl) ∘ₖ
      pairSurvivingHistory a n v H := by
  unfold pairSurvivingHistory
  rw [← rawExtension_restrict_comp (show a ≤ a+2*n by omega) (show a+2*n ≤ a+2*(n+1) by omega)
    (noPairHits_measurable a n (a+2*n) le_rfl v H)
    (pairHitTest_measurable a n (a+2*(n+1)) (by omega) v H).compl]
  congr 1
  rw [noPairHits_prefix,noPairHits_succ]

theorem pairStoppedHistory_factor (a n : ℕ) (v H : ℝ) :
    pairStoppedHistory a n v H=
      ((rawExtension (a+2*n) (a+2*n+1)).restrict
        (pairHitTest_measurable a n (a+2*n+1) le_rfl v H)) ∘ₖ pairSurvivingHistory a n v H := by
  unfold pairStoppedHistory pairSurvivingHistory
  rw [← rawExtension_restrict_comp (show a ≤ a+2*n by omega) (show a+2*n ≤ a+2*n+1 by omega)
    (noPairHits_measurable a n (a+2*n) le_rfl v H)
    (pairHitTest_measurable a n (a+2*n+1) le_rfl v H)]
  congr 1

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
