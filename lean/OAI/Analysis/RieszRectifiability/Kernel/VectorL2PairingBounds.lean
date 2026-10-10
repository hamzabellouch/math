import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.L2Pairings

namespace OAI

/-!
A vector-valued L² norm estimate controls each scalar pairing against a fixed direction.
The proof combines pointwise inner-product bounds with the L² Cauchy–Schwarz inequality.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

theorem toLp_norm_eq_sqrt_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  rw [← toLp_norm_sq_eq_integral μ f hf, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem scalar_L2_pairing_of_vector_norm_bound {X : Type*} [MeasurableSpace X] {d : ℕ}
    (μ : Measure X) (f g : X → ℝ) (F : X → Ambient d)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hF : MemLp F 2 μ)
    (D : ℝ≥0) (hN : eLpNorm F 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) (e : Ambient d) :
    Integrable (fun x => g x * inner ℝ e (F x)) μ ∧
      |∫ x, g x * inner ℝ e (F x) ∂μ| ≤
        (‖e‖ * (D : ℝ)) * Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  let u := fun x => inner ℝ e (F x)
  have hpoint : ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖e‖ * ‖F x‖ :=
    Filter.Eventually.of_forall fun x => norm_inner_le_norm (𝕜 := ℝ) e (F x)
  have hum : AEStronglyMeasurable u μ :=
    aestronglyMeasurable_const.inner hF.aestronglyMeasurable
  have hu : MemLp u 2 μ := hF.of_le_mul hum hpoint
  have hNu : eLpNorm u 2 μ ≤
      ENNReal.ofReal ‖e‖ * ((D : ℝ≥0∞) * eLpNorm f 2 μ) :=
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hum hpoint 2).trans
      (mul_le_mul_right hN (ENNReal.ofReal ‖e‖))
  have hfin : ENNReal.ofReal ‖e‖ * ((D : ℝ≥0∞) * eLpNorm f 2 μ) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hf.eLpNorm_ne_top)
  have hnorm : ‖hu.toLp u‖ ≤ ‖e‖ * ((D : ℝ) * ‖hf.toLp f‖) := by
    simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg e),
      ENNReal.coe_toReal] using! ENNReal.toReal_mono hfin hNu
  refine ⟨memLp_one_iff_integrable.mp (hg.mul hu), ?_⟩
  rw [← toLp_inner_eq_integral μ g u hg hu]
  have hi : |inner ℝ (hg.toLp g) (hu.toLp u)| ≤ ‖hg.toLp g‖ * ‖hu.toLp u‖ := by
    simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) (hg.toLp g) (hu.toLp u)
  calc
    _ ≤ ‖hg.toLp g‖ * (‖e‖ * ((D : ℝ) * ‖hf.toLp f‖)) :=
      hi.trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
    _ = _ := by
      rw [toLp_norm_eq_sqrt_integral μ g hg, toLp_norm_eq_sqrt_integral μ f hf]
      ring

end

end RieszRectifiability

end OAI
