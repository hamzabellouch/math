import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStrip
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaChartEnergyDomination
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! Exact quotient integration on the half-open arithmetic cusp strip.
This identifies the cusp mass and energy with their global restrictions,
including the boundary convention of the horizontal period cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInjective_map_restrict {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hi : InjOn cubicThetaQuotientMap S) :
    (cubicThetaPointMeasure.restrict S).map cubicThetaQuotientMap=
      cubicThetaQuotientMeasure.restrict (cubicThetaQuotientMap '' S) := by
  ext B hB
  have hT := (hB.preimage cubicThetaQuotientMap_open.continuous.measurable).inter hS
  have hTi := hi.mono (inter_subset_right : cubicThetaQuotientMap ⁻¹' B ∩ S⊆S)
  rw [Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage cubicThetaQuotientMap_open.continuous.measurable),
    ← cubicThetaQuotientMeasure_local_image hT
      (cubicThetaQuotient_injective_image_measurable hT hTi) hTi,
    Set.image_preimage_inter,Measure.restrict_apply hB]

lemma cubicThetaInjective_integral {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hi : InjOn cubicThetaQuotientMap S)
    (f : CubicThetaQuotient → ℝ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' S, f q ∂cubicThetaQuotientMeasure)=
      ∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure := by
  rw [← cubicThetaInjective_map_restrict hS hi]
  exact integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable hf

lemma cubicThetaCuspStrip_integral {H : ℝ} (hH : 1≤H)
    (f : CubicThetaQuotient → ℝ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' cubicThetaCuspStrip H, f q ∂cubicThetaQuotientMeasure)=
      ∫ p in cubicThetaCuspStrip H, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure :=
  cubicThetaInjective_integral (cubicThetaCuspStrip_measurable H)
    (cubicThetaCuspStrip_injective hH) f hf

lemma cubicThetaInjective_integral_le {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hi : InjOn cubicThetaQuotientMap S)
    {f : CubicThetaQuotient → ℝ} (hf : Integrable f cubicThetaQuotientMeasure)
    (hn : ∀ q, 0≤f q) :
    (∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure)≤
      ∫ q, f q ∂cubicThetaQuotientMeasure := by
  have hm : (cubicThetaPointMeasure.restrict S).map cubicThetaQuotientMap≤
      cubicThetaQuotientMeasure := by
    rw [cubicThetaInjective_map_restrict hS hi]
    exact Measure.restrict_le_self
  rw [← integral_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (hf.aestronglyMeasurable.mono_measure hm)]
  exact integral_mono_measure hm (ae_of_all _ hn) hf

theorem cubicThetaCuspStrip_energy_le {H : ℝ} (hH : 1≤H) (F : cubicThetaSmoothTests) :
    (∫ p in cubicThetaCuspStrip H,
      cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+cubicThetaSectionEnergy F p
        ∂cubicThetaPointMeasure)≤‖cubicThetaGlobalEnergyTest F‖^2 := by
  rw [cubicThetaGlobalEnergyTest_norm_sq]
  simp only [cubicThetaSectionRepresentative_norm]
  have h := cubicThetaInjective_integral_le (cubicThetaCuspStrip_measurable H)
    (cubicThetaCuspStrip_injective hH) (cubicThetaIntrinsicEnergy_integrable F)
    (fun q => add_nonneg (sq_nonneg _) (cubicThetaQuotientEnergy_nonneg F q))
  simpa only [cubicThetaQuotientEnergy_apply] using h

end CubicFirstMoment

end

end OAI
