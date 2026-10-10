import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeL1

namespace OAI

/-! L1 and uniform bounds for the integrable time averages used in the
very-short-time error. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem kernelAverage_l1 (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (F : ℝ×(ℝ×ℝ) → ℂ) (hFm : Measurable F) (B : ℝ)
    (hF : ∀ t, Integrable (fun z => F (t,z)) planeMeasure)
    (hbound : ∀ t, (∫ z, ‖F (t,z)‖ ∂planeMeasure)≤B) :
    Integrable (fun z => ∫ t, K t*F (t,z)) planeMeasure ∧
      (∫ z, ‖∫ t, K t*F (t,z)‖ ∂planeMeasure)≤(∫ t, ‖K t‖)*B := by
  let H := fun p : ℝ×(ℝ×ℝ) => K p.1*F p
  have hHm : Measurable H := (hKm.comp measurable_fst).mul hFm
  have hHi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t => (hF t).const_mul (K t)
    · apply (hK.norm.mul_const B).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      change ‖∫ z, ‖K t*F (t,z)‖ ∂planeMeasure‖≤_
      simp only [norm_mul,integral_const_mul]
      rw [Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)
  refine ⟨hHi.integral_prod_right,?_⟩
  calc
    _ ≤ ∫ z : ℝ×ℝ, (∫ t, ‖H (t,z)‖) ∂planeMeasure :=
      integral_mono hHi.integral_prod_right.norm hHi.norm.integral_prod_right
        (fun z => norm_integral_le_integral_norm _)
    _ = ∫ t, ∫ z, ‖H (t,z)‖ ∂planeMeasure :=
      integral_integral_swap (f:=fun (z : ℝ×ℝ) (t : ℝ) => ‖H (t,z)‖) hHi.norm.swap
    _ ≤ ∫ t, ‖K t‖*B := by
      apply integral_mono hHi.norm.integral_prod_left (hK.norm.mul_const B)
      intro t
      simp only [H,norm_mul,integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)
    _ = _ := integral_mul_const B _

theorem kernelAverage_uniform (K : ℝ → ℂ) (hK : Integrable K)
    (F : ℝ×(ℝ×ℝ) → ℂ) (C : ℝ) (hF : ∀ t z, ‖F (t,z)‖≤C) (z : ℝ×ℝ) :
    ‖∫ t, K t*F (t,z)‖≤(∫ t, ‖K t‖)*C := by
  have h := norm_integral_le_of_norm_le (hK.norm.mul_const C)
    (Filter.Eventually.of_forall fun t => show ‖K t*F (t,z)‖≤‖K t‖*C from by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hF t z) (norm_nonneg _))
  simpa only [integral_mul_const] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
