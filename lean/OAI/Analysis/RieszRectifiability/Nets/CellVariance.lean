import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

def cellMean (μ : Measure X) (w : X → ℝ) : ℝ :=
  (∫ x, w x ∂μ) / μ.real univ

theorem integral_sq_sub_const (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (a : ℝ) :
    (∫ x, (w x - a) ^ 2 ∂μ) = (∫ x, w x ^ 2 ∂μ) -
      2 * (∫ x, w x ∂μ) * a + μ.real univ * a ^ 2 := by
  have h := integral_squared_difference μ w (fun _ => a) hw.integrable_sq
    ((hw.integrable (by norm_num)).mul_const a) (integrable_const _)
  simpa only [integral_mul_const, integral_const, smul_eq_mul, mul_assoc] using! h

theorem pairwise_square_integrable_right (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (x : X) :
    Integrable (fun y => (w x - w y) ^ 2) μ :=
  ((memLp_const (w x)).sub hw).integrable_sq

theorem inner_pairwise_square_formula (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (x : X) :
    (∫ y, (w x - w y) ^ 2 ∂μ) = (∫ y, w y ^ 2 ∂μ) -
      2 * (∫ y, w y ∂μ) * w x + μ.real univ * w x ^ 2 := by
  have heq : (fun y => (w x - w y) ^ 2) = (fun y => (w y - w x) ^ 2) := by
    funext y
    ring
  rw [heq]
  exact integral_sq_sub_const μ w hw (w x)

theorem iterated_pairwise_square_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) :
    Integrable (fun x => ∫ y, (w x - w y) ^ 2 ∂μ) μ := by
  simp_rw [inner_pairwise_square_formula μ w hw]
  exact ((integrable_const _).sub ((hw.integrable (by norm_num)).const_mul _)).add
    (hw.integrable_sq.const_mul _)

theorem iterated_pairwise_square_formula (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) :
    (∫ x, ∫ y, (w x - w y) ^ 2 ∂μ ∂μ) =
      2 * μ.real univ * (∫ x, w x ^ 2 ∂μ) - 2 * (∫ x, w x ∂μ) ^ 2 := by
  simp_rw [inner_pairwise_square_formula μ w hw]
  have hsub := integral_sub (integrable_const (∫ y, w y ^ 2 ∂μ))
    ((hw.integrable (by norm_num)).const_mul (2 * (∫ y, w y ∂μ)))
  have hadd := integral_add
    ((integrable_const (∫ y, w y ^ 2 ∂μ)).sub
      ((hw.integrable (by norm_num)).const_mul (2 * (∫ y, w y ∂μ))))
    (hw.integrable_sq.const_mul (μ.real univ))
  simp only [Pi.sub_apply] at hadd
  rw [hadd, hsub, integral_const_mul, integral_const_mul, integral_const]
  simp only [smul_eq_mul]
  ring

theorem cell_variance_eq_half_pairwise (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (hμ : μ.real univ ≠ 0) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) =
      (∫ x, ∫ y, (w x - w y) ^ 2 ∂μ ∂μ) / (2 * μ.real univ) := by
  rw [integral_sq_sub_const μ w hw, iterated_pairwise_square_formula μ w hw]
  unfold cellMean
  field_simp [hμ]
  ring

end

end RieszRectifiability

end OAI
