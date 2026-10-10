import Mathlib

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace CriticalPercolation
variable {X : Type*} [MeasurableSpace X]

lemma lintegral_fourth_bound_of_tendsto (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (g : X → ℝ≥0∞) (C : ℝ≥0∞) (hm : ∀ n, Measurable (f n))
    (ht : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hb : ∀ n, (∫⁻ x, f n x ∂μ)^4≤C) : (∫⁻ x, g x ∂μ)^4≤C := by
  have hroot (n : ℕ) : (∫⁻ x, f n x ∂μ) ≤ C^((4:ℝ)⁻¹) := by
    apply (ENNReal.le_rpow_inv_iff (by norm_num : (0:ℝ)<4)).mpr
    simpa only [ENNReal.rpow_ofNat] using hb n
  have hlim : (∫⁻ x, g x ∂μ) ≤ C^((4:ℝ)⁻¹) := by
    calc _ = ∫⁻ x, liminf (fun n => f n x) atTop ∂μ := by
               apply lintegral_congr
               intro x
               exact (ht x).liminf_eq.symm
         _ ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := lintegral_liminf_le hm
         _ ≤ C^((4:ℝ)⁻¹) :=
           liminf_le_of_frequently_le (Eventually.frequently (Eventually.of_forall hroot))
  have h := (ENNReal.le_rpow_inv_iff (by norm_num : (0:ℝ)<4)).mp hlim
  simpa only [ENNReal.rpow_ofNat] using h

end CriticalPercolation
end
end

end OAI
