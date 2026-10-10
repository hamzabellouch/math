import OAI.Analysis.LipschitzHilbert.Estimates.MihlinTimeCommutator
import OAI.Analysis.LipschitzHilbert.Estimates.PrincipalValueProfileCommutator

namespace OAI

/-! Actual full-input principal-value/multiplier commutators with a
uniform Mihlin bound and no frequency restriction on the input. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpVerticalCommutator_mihlin_bound (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (hu : ∀ x, LipschitzWith 1 (fun y => u (x,y))) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    eLpNorm (sharpVerticalCommutator m 1 0 epsilon R u f) 2 planeMeasure≤
      ENNReal.ofReal ((32*lineCommutatorNormConstant*A*R)*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨hF,henergy⟩ := sharpVerticalCommutator_mihlin_energy m A hA hm epsilon R he hR u hum hu hub f
  have hi : ‖f.toLp 2 planeMeasure‖^2=∫ z, ‖f z‖^2 ∂planeMeasure :=
    memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)
  rw [←memLp_toL2_norm_sq planeMeasure _ hF,←hi] at henergy
  have hn : ‖hF.toLp (sharpVerticalCommutator m 1 0 epsilon R u f)‖≤
      (32*lineCommutatorNormConstant*A*R)*‖f.toLp 2 planeMeasure‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by have := lineCommutatorNormConstant_nonneg; positivity)).mp
    simpa only [mul_pow] using henergy
  rw [←Lp.enorm_toLp hF,←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

theorem principalValueProfileCommutator_mihlin_bound (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (hufiber : ∀ x, LipschitzWith 1 (fun y => u (x,y))) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (principalValueProfileCommutator m 1 0 R u f) 2 planeMeasure ∧
    eLpNorm (principalValueProfileCommutator m 1 0 R u f) 2 planeMeasure≤
      ENNReal.ofReal ((32*lineCommutatorNormConstant*A*R)*‖f.toLp 2 planeMeasure‖) := by
  have hmeas := principalValueProfileCommutator_measurable m 1 0 R hR hRsmall u hu.continuous.measurable f
  have hb : eLpNorm (principalValueProfileCommutator m 1 0 R u f) 2 planeMeasure≤
      ENNReal.ofReal ((32*lineCommutatorNormConstant*A*R)*‖f.toLp 2 planeMeasure‖) := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u:=(atTop : Filter ℕ))
      (Eventually.of_forall fun n => sharpVerticalCommutator_mihlin_bound m A hA hm
        (pvInnerRadius R n) R (pvInnerRadius_pos R hR n) hR u hu.continuous.measurable hufiber hub f)
      (fun n => (sharpVerticalCommutator_mihlin_energy m A hA hm
        (pvInnerRadius R n) R (pvInnerRadius_pos R hR n) hR u hu.continuous.measurable hufiber hub f).1.aestronglyMeasurable)
      hmeas.aestronglyMeasurable
    exact Eventually.of_forall (sharpVerticalCommutator_tendsto m 1 0 R (by norm_num) hR hRsmall
      u hu.continuous.measurable hub f)
  exact ⟨hb.trans_lt (by simp),hb⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
