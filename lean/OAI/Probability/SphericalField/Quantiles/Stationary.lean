import Mathlib
import OAI.Probability.SphericalField.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma BoundedField.toQuantile_monotone {B : ℝ} (q : BoundedField B) (hB : B ≤ 1) :
    Monotone (q.toQuantile hB) := fun _ _ h => q.monotone h

lemma quantileA_abs_sub_le {B r s : ℝ} (q : Time → Time) (hq : Measurable q)
    (hB : B < 1) (hb : ∀ᵐ u ∂timeLaw, (q u:ℝ) ≤ B)
    (hr : r ∈ Icc 0 B) (hs : s ∈ Icc 0 B) :
    |quantileA q r-quantileA q s| ≤ (1/(1-B)^2)*|r-s| := by
  have hc := quantileA_integrand_continuous q hq hB hb
  unfold quantileA
  rw [intervalIntegral.integral_interval_sub_left
    ((hc.mono (Icc_subset_Icc le_rfl hr.2)).intervalIntegrable_of_Icc hr.1)
    ((hc.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := r)
    (f := fun t => 1/(quantileTail q t)^2) (C := 1/(1-B)^2) (fun t ht => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/(quantileTail q t)^2)]
      exact quantileA_integrand_bound q hq hB hb (ht.2.trans (max_le hs.2 hr.2)))
  simpa only [Real.norm_eq_abs] using h

end SphericalPerceptron
end
end

end OAI
