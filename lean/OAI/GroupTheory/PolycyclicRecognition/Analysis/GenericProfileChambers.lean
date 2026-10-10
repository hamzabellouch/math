import OAI.GroupTheory.PolycyclicRecognition.Analysis.GenericProfileSigns
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightChamberAction

namespace OAI

/-! # Generic profile lines have one image chamber

The scalar variation equalities give constant signs. Positive weight-ray
preservation, for a template symmetry and its inverse, upgrades those signs
to agreement of the entire image of the closed chamber.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set Filter

variable {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

theorem templateSymmetry_preservesPositiveWeightRays
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (A : templateSymmetryGroup D) :
    PreservesPositiveWeightRays (fun i => (D.weight i).toContinuousLinearMap) A.val := by
  intro i
  exact templateSymmetry_weight_ray D A i (hweights i)

theorem generic_profile_chamber_agreement
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (h q : ℝ → W) (hc : Continuous h) (w : W) (hw : ∀ i, D.weight i w ≠ 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hq : ∀ i, IntervalIntegrable (fun t => D.weight i (q t)) volume 0 T)
    (hFTC : ∀ i t, t ∈ Icc 0 T →
      D.weight i (h t) = ∫ s in 0..t, D.weight i (q s))
    (label : ℝ → templateSymmetryGroup D)
    (hlabel : ∀ᵐ t ∂volume.restrict (Icc 0 T), q t = (label t).val w)
    (hlower : T * D.segmentSupport w ≤ D.templateSupport (h '' Icc 0 T)) :
    ∀ᵐ s ∂volume.restrict (Ioc 0 T), ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (label s).val '' closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
          (weightSigns (fun i => (D.weight i).toContinuousLinearMap) w) =
        (label t).val '' closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
          (weightSigns (fun i => (D.weight i).toContinuousLinearMap) w) := by
  obtain ⟨S, hS⟩ := generic_profile_signs_constant D hweights h q hc w hw hT hq hFTC
    label hlabel hlower
  have hlabel' : ∀ᵐ t ∂volume.restrict (Ioc 0 T), q t = (label t).val w :=
    hlabel.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  filter_upwards [hS, hlabel'] with s hs hqs
  filter_upwards [hS, hlabel'] with t ht hqt
  apply image_closedWeightChamber_eq_of_signs _ _ _
    (templateSymmetry_preservesPositiveWeightRays D hweights (label s))
    (templateSymmetry_preservesPositiveWeightRays D hweights (label s)⁻¹)
    (templateSymmetry_preservesPositiveWeightRays D hweights (label t))
    (templateSymmetry_preservesPositiveWeightRays D hweights (label t)⁻¹) hw
  intro i
  change 0 < D.weight i ((label s).val w) ↔ 0 < D.weight i ((label t).val w)
  rw [← hqs, ← hqt]
  exact (hs i).trans (ht i).symm

end PolycyclicRecognition.SupportDatum

end

end OAI
