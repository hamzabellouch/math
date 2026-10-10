import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainPullback

namespace OAI

/-! # Integrating a collision parameter block in physical time, thermal, plane order -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

def splitStage : StageControls ≃ᵐ ℝ × (V × V) :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm)

theorem splitStage_apply (p : StageControls) : splitStage p = (p.1.1,p.2,p.1.2) := rfl

theorem splitStage_measurePreserving : MeasurePreserving splitStage :=
  (measurePreserving_prodAssoc volume volume volume).trans
    ((MeasurePreserving.id volume).prod
      (Measure.measurePreserving_swap (μ := volume) (ν := volume)))

theorem lintegral_stage {F : StageControls → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p) = ∫⁻ t : ℝ, ∫⁻ w : V, ∫⁻ L : V, F ((t,L),w) := by
  have h : Measurable (fun p : ℝ × (V × V) => F (splitStage.symm p)) :=
    hF.comp splitStage.symm.measurable
  calc
    _ = ∫⁻ p : ℝ × (V × V), F (splitStage.symm p) :=
      (splitStage_measurePreserving.symm.lintegral_comp hF).symm
    _ = ∫⁻ t : ℝ, ∫⁻ p : V × V, F (splitStage.symm (t,p)) := by
      rw [Measure.volume_eq_prod]
      exact lintegral_prod _ h.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro t
      rw [Measure.volume_eq_prod]
      exact lintegral_prod _ ((h.comp measurable_prodMk_left).aemeasurable)

end BoltzmannNonuniqueness.FiveGainMap

end

end OAI
