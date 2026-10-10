import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # Positive powers of a bounded product of two L2 functions -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}

theorem bounded_product_power_integrable (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {A B : ℝ} (ha : ∀ᵐ x ∂μ, |f x| ≤ A) (hb : ∀ᵐ x ∂μ, |g x| ≤ B)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) {q : ℕ} (hq : 1 ≤ q) :
    Integrable (fun x => (f x*g x)^q) μ := by
  have hi : Integrable (fun x => f x*g x) μ := hf.integrable_mul hg
  apply (hi.norm.const_mul ((A*B)^(q-1))).mono' ((hf.aestronglyMeasurable.mul hg.aestronglyMeasurable).pow q)
  filter_upwards [ha,hb] with x hax hbx
  have hbound : |f x*g x| ≤ A*B := by
    rw [abs_mul]
    exact mul_le_mul hax hbx (abs_nonneg _) hA
  change ‖(f x*g x)^q‖ ≤ (A*B)^(q-1)*‖f x*g x‖
  simp only [Real.norm_eq_abs,abs_pow]
  calc
    |f x*g x|^q = |f x*g x|^(q-1)*|f x*g x| := by
      rw [← pow_succ]
      congr 1
      omega
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) hbound (q-1)) (abs_nonneg _)

end RegularPointCoordinates

end

end OAI
