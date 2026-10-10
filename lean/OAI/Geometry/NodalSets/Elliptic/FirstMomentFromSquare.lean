import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

namespace Yau.Analysis
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma lintegral_enorm_le_of_square {f : Ω → ℝ} (hf : MemLp f 2 μ)
    {C : ℝ} (hC : (∫ a, (f a)^2 ∂μ) ≤ C) :
    (∫⁻ a, ‖f a‖ₑ ∂μ) ≤ ENNReal.ofReal (C+1) := by
  have hi : Integrable f μ := hf.integrable (by norm_num)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ a, ‖f a‖ ∂μ) ≤ ∫ a, (f a)^2+1 ∂μ := by
      apply integral_mono hi.norm (hf.integrable_sq.add (integrable_const 1))
      intro a
      change |f a| ≤ (f a)^2+1
      nlinarith [sq_nonneg (|f a|-1),sq_abs (f a)]
    _ = (∫ a, (f a)^2 ∂μ)+1 := by rw [integral_add hf.integrable_sq (integrable_const 1)]; simp
    _ ≤ C+1 := by linarith

end Yau.Analysis

end OAI
