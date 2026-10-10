import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalQuotientMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCutoffEnergy

namespace OAI

/-! An injective chart cannot contribute more intrinsic energy than the
whole quotient. Only the proved local measure identity is used here. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaChart_measure_le
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source) :
    (cubicThetaPointMeasure.restrict S).map cubicThetaQuotientMap≤cubicThetaQuotientMeasure := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage cubicThetaQuotientMap_open.continuous.measurable)]
  rw [← cubicThetaQuotientMeasure_chart e he
    ((hB.preimage cubicThetaQuotientMap_open.continuous.measurable).inter hS)
    (fun _ hx => hSe hx.2)]
  apply measure_mono
  rintro q ⟨p,hp,rfl⟩
  exact hp.1

lemma cubicThetaChart_integral_le
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source)
    {f : CubicThetaQuotient → ℝ} (hf : Integrable f cubicThetaQuotientMeasure)
    (hn : ∀ q, 0≤f q) :
    (∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure)≤
      ∫ q, f q ∂cubicThetaQuotientMeasure := by
  have hm := cubicThetaChart_measure_le e he hS hSe
  rw [← integral_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (hf.aestronglyMeasurable.mono_measure hm)]
  exact integral_mono_measure hm (Filter.Eventually.of_forall hn) hf

lemma cubicThetaQuotientEnergy_nonneg (F : cubicThetaSmoothTests) (q : CubicThetaQuotient) :
    0≤cubicThetaQuotientEnergy F q :=
  mul_nonneg (sq_nonneg _) (cubicThetaTangentEnergy_nonneg _)

lemma cubicThetaIntrinsicEnergy_integrable (F : cubicThetaSmoothTests) :
    Integrable (fun q => cubicThetaSectionNorm F q^2+cubicThetaQuotientEnergy F q)
      cubicThetaQuotientMeasure := by
  have hm : Integrable (fun q => cubicThetaSectionNorm F q^2) cubicThetaQuotientMeasure := by
    have h := (cubicThetaSectionRepresentative_memLp F).integrable_norm_pow (by norm_num)
    simpa only [cubicThetaSectionRepresentative_norm] using h
  have hd : Integrable (cubicThetaQuotientEnergy F) cubicThetaQuotientMeasure :=
    (cubicThetaQuotientEnergy_continuous F).integrable_of_hasCompactSupport
      (cubicThetaQuotientEnergy_compact F)
  exact hm.add hd

theorem cubicThetaChart_energy_le
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source)
    (F : cubicThetaSmoothTests) :
    (∫ p in S, cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+
      cubicThetaSectionEnergy F p ∂cubicThetaPointMeasure)≤
        ‖cubicThetaGlobalEnergyTest F‖^2 := by
  rw [cubicThetaGlobalEnergyTest_norm_sq]
  simp only [cubicThetaSectionRepresentative_norm]
  have h := cubicThetaChart_integral_le e he hS hSe
    (cubicThetaIntrinsicEnergy_integrable F)
    (fun q => add_nonneg (sq_nonneg _) (cubicThetaQuotientEnergy_nonneg F q))
  simpa only [cubicThetaQuotientEnergy_apply] using h

end CubicFirstMoment

end

end OAI
