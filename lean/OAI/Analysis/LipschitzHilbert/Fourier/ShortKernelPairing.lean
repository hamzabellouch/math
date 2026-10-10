import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeL1

namespace OAI

/-! Restricted mass bounds for an integrable short-time kernel error. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortKernel_pairing (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f planeMeasure) (hg : Integrable g planeMeasure)
    (hf1 : ∀ z, ‖f z‖≤1) (hg1 : ∀ z, ‖g z‖≤1) :
    Integrable (fun z => shortSlopeOperator K u f z*star (g z)) planeMeasure ∧
    ‖∫ z, shortSlopeOperator K u f z*star (g z) ∂planeMeasure‖≤
      min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)*(∫ t, ‖K t‖) := by
  have hA := shortSlopeOperator_l1 K hKm hK u hu f hfm hf
  have hm := shortSlopeOperator_measurable K hKm u hu.continuous.measurable f hfm
  have hp (z : ℝ×ℝ) : ‖shortSlopeOperator K u f z*star (g z)‖≤‖shortSlopeOperator K u f z‖ := by
    rw [norm_mul,norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (hg1 z)
  have hi := hA.1.norm.mono' (show Measurable (fun z => shortSlopeOperator K u f z*star (g z)) from by fun_prop).aestronglyMeasurable (Filter.Eventually.of_forall hp)
  refine ⟨hi,?_⟩
  rw [min_mul_of_nonneg _ _ (integral_nonneg fun _ => norm_nonneg _)]
  apply le_min
  · calc
      _ ≤ ∫ z, ‖shortSlopeOperator K u f z‖ ∂planeMeasure :=
        norm_integral_le_of_norm_le hA.1.norm (Filter.Eventually.of_forall hp)
      _ ≤ _ := hA.2.trans_eq (by ring)
  · have hp' (z : ℝ×ℝ) : ‖shortSlopeOperator K u f z*star (g z)‖≤
        (∫ t, ‖K t‖)*‖g z‖ := by
      rw [norm_mul,norm_star]
      have hb := shortSlopeOperator_uniform K hK u f 1 (by norm_num) hf1 z
      simp only [one_mul] at hb
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    have h := norm_integral_le_of_norm_le (hg.norm.const_mul (∫ t, ‖K t‖))
      (Filter.Eventually.of_forall hp')
    simpa only [integral_const_mul,integral_mul_const,mul_comm] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
