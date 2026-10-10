import OAI.Analysis.CircleDomains.Sobolev.ClosedDiskIntegral
import OAI.Analysis.CircleDomains.Selection.OuterContours

namespace OAI

/-! Exact subtraction of finitely many disjoint round holes from a
Jordan-domain area integral. -/
open Set Function MeasureTheory Metric
open scoped BigOperators
noncomputable section
namespace CircleDomainRigidity

lemma integral_finite_round_holes (H : ℂ ≃ₜ ℂ) {n : ℕ}
    (c : Fin n → ℂ) (r : Fin n → ℝ)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H)
    {q : ℂ → ℝ} (hq : Continuous q) :
    (∫ z in jordanInterior H, q z) - ∑ i, ∫ z in ball (c i) (r i), q z =
      ∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), q z := by
  have hj : IntegrableOn q (jordanInterior H) :=
    (hq.continuousOn.integrableOn_compact (isCompact_closure_jordanInterior H)).mono_set subset_closure
  have hcb (i : Fin n) : IntegrableOn q (closedBall (c i) (r i)) := hj.mono_set (hin i)
  have hsame (i : Fin n) : (∫ z in closedBall (c i) (r i), q z) =
      ∫ z in ball (c i) (r i), q z := by
    simpa only [univ_inter] using integral_inter_closedBall_eq_ball univ (c i) (r i) q
  rw [setIntegral_sdiff (MeasurableSet.iUnion fun _ => isClosed_closedBall.measurableSet)
    hj (iUnion_subset hin),integral_iUnion_fintype
      (fun _ => isClosed_closedBall.measurableSet) hd hcb]
  simp_rw [hsame]

end CircleDomainRigidity

end

end OAI
