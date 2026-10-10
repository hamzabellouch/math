import OAI.Probability.InvariantIsing.Spectral.PositiveResolventContraction
import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResolventEquation

namespace OAI

/-! Removing one physical Gaussian column changes the normalized transform by at most 1/(Nt). -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma gaussianGramLeaveResolvent_trace_gap {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) :
    0 ≤ (gaussianGramLeaveResolvent t z j).trace-(gaussianGramResolvent t z).trace ∧
    (gaussianGramLeaveResolvent t z j).trace-(gaussianGramResolvent t z).trace ≤ 1/t := by
  rw [gaussianGramLeaveResolvent_trace ht z j]
  let x := gaussianPatternScaledColumn z j
  let y := gaussianGramLeaveResolvent t z j *ᵥ x
  have hq := gaussianGramColumnQuadratic_nonneg ht z j
  change 0 ≤ x ⬝ᵥ y at hq
  have hd : 0 < 1+x ⬝ᵥ y := by linarith
  have hy : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg (fun i _ => mul_self_nonneg (y i))
  have hc := positiveResolvent_quadratic_contraction ht (gaussianGramLeaveOneOut_posSemidef z j) x
  change t*(y ⬝ᵥ y) ≤ x ⬝ᵥ y at hc
  constructor
  · exact div_nonneg hy hd.le
  · apply (div_le_div_iff₀ hd ht).mpr
    nlinarith

end InvariantIsing

end

end OAI
