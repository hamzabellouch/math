import OAI.Analysis.CircleDomains.Probability.SliceMeasurability
import OAI.Analysis.CircleDomains.Sobolev.IntegralLineAbsoluteContinuity

namespace OAI

/-! Local ACL gives a measurable representative on the open rectangle.
This avoids any analyticity assumption on the finite-chain infimum. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem aestronglyMeasurable_on_rectangle_of_ACL
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hh : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hv : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d) :
    AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)) := by
  let U := Ioo a b
  let V := Ioo c d
  let μ : Measure U := volume.comap ((↑) : U → ℝ)
  let ν : Measure V := volume.comap ((↑) : V → ℝ)
  obtain ⟨u, hau, hub⟩ := exists_between hab
  let : Nonempty U := ⟨⟨u, hau, hub⟩⟩
  let : μ.IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume isOpen_Ioo.isOpenEmbedding_subtypeVal
  have hμuniv : μ univ = volume U := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioo).comap_apply]
    simp only [image_univ, Subtype.range_coe]
    rfl
  have hνuniv : ν univ = volume V := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioo).comap_apply]
    simp only [image_univ, Subtype.range_coe]
    rfl
  let : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact measure_Ioo_lt_top⟩
  let : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact measure_Ioo_lt_top⟩
  have hhv : ∀ᵐ y ∂ν, Continuous fun x : U => f (x.val, y.val) := by
    have h := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hh
    have h' : ∀ᵐ y : V ∂ν, AbsolutelyContinuousOnInterval (fun x => f (x, y.val)) a b :=
      (ae_restrict_iff_subtype (s := V) measurableSet_Ioo).mp h
    filter_upwards [h'] with y hy
    have hc : ContinuousOn (fun x => f (x, y.val)) (Icc a b) := by
      simpa only [uIcc_of_le hab.le] using hy.continuousOn
    exact (hc.mono Ioo_subset_Icc_self).domRestrict
  have hvh : ∀ᵐ x ∂μ, Continuous fun y : V => f (x.val, y.val) := by
    have h := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hv
    have h' : ∀ᵐ x : U ∂μ, AbsolutelyContinuousOnInterval (fun y => f (x.val, y)) c d :=
      (ae_restrict_iff_subtype (s := U) measurableSet_Ioo).mp h
    filter_upwards [h'] with x hx
    have hc : ContinuousOn (fun y => f (x.val, y)) (Icc c d) := by
      simpa only [uIcc_of_le hcd.le] using hx.continuousOn
    exact (hc.mono Ioo_subset_Icc_self).domRestrict
  have hF : AEStronglyMeasurable (fun p : U × V => f (p.1.val, p.2.val)) (μ.prod ν) :=
    aestronglyMeasurable_of_ae_continuous_slices μ ν _ hvh hhv
  have hmap : (μ.prod ν).map (Prod.map ((↑) : U → ℝ) ((↑) : V → ℝ)) =
      volume.restrict (Ioo a b ×ˢ Ioo c d) := by
    rw [← Measure.map_prod_map μ ν measurable_subtype_coe measurable_subtype_coe,
      map_comap_subtype_coe measurableSet_Ioo, map_comap_subtype_coe measurableSet_Ioo,
      Measure.prod_restrict]
    rfl
  rw [← hmap]
  exact ((MeasurableEmbedding.subtype_coe measurableSet_Ioo).prodMap
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo)).aestronglyMeasurable_map_iff.mpr hF

end CircleDomainRigidity

end

end OAI
