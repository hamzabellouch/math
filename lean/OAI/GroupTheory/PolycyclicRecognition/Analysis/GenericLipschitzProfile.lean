import OAI.GroupTheory.PolycyclicRecognition.Analysis.GenericProfileChambers
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LipschitzProfileFTC

namespace OAI

/-! # Generic chamber agreement from actual Lipschitz line derivatives -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set Filter
open scoped NNReal

theorem generic_lipschitz_profile_chamber_agreement
    {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (h : ℝ → W) (hc : Continuous h) (hzero : h 0 = 0)
    (w : W) (hw : ∀ i, D.weight i w ≠ 0) {T : ℝ} (hT : 0 ≤ T)
    {C : ℝ≥0} (hlip : LipschitzOnWith C h (Icc 0 T))
    (label : ℝ → templateSymmetryGroup D)
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt h ((label t).val w) t)
    (hlower : T * D.segmentSupport w ≤ D.templateSupport (h '' Icc 0 T)) :
    ∀ᵐ s ∂volume.restrict (Ioc 0 T), ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (label s).val '' closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
          (weightSigns (fun i => (D.weight i).toContinuousLinearMap) w) =
        (label t).val '' closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
          (weightSigns (fun i => (D.weight i).toContinuousLinearMap) w) := by
  obtain ⟨hq, hFTC⟩ := profile_weight_fundamental_identities
    (fun i => (D.weight i).toContinuousLinearMap) hT hlip hderiv
  apply generic_profile_chamber_agreement D hweights h (fun t => (label t).val w)
    hc w hw hT hq _ label (Eventually.of_forall (fun _ => rfl)) hlower
  intro i t ht
  have hh := hFTC i t ht
  change D.weight i (h t - h 0) = ∫ s in 0..t, D.weight i ((label s).val w) at hh
  simpa only [hzero, sub_zero] using hh

end PolycyclicRecognition.SupportDatum

end

end OAI
