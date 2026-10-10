import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CollarLpPullback

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma sourceAngularCollar_measurePreserving (l r : ℝ) :
    MeasurePreserving (Function.uncurry sourceAngularCollar) (sourceCylinderMeasure l r)
      (sourceAngularCollarMeasure l r) := by
  refine ⟨continuous_uncurry_sourceAngularCollar.measurable,?_⟩
  rw [sourceCylinderMeasure_eq]
  rfl

def sourceCylinderPullback {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Lp ℂ 2 (sourcePhysicalCollarMeasure l r) →L[ℝ]
      Lp ℂ 2 (sourceCylinderMeasure l r) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (Function.uncurry sourceAngularCollar)
    (sourceAngularCollar_measurePreserving l r)).toContinuousLinearMap.comp
      (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (sourceAngularCollarMeasure_le hlr hl hr))

lemma sourceCylinderPullback_ae {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (f : Lp ℂ 2 (sourcePhysicalCollarMeasure l r)) :
    sourceCylinderPullback hlr hl hr f=ᵐ[sourceCylinderMeasure l r]
      f ∘ Function.uncurry sourceAngularCollar := by
  apply (Lp.coeFn_compMeasurePreserving _ (sourceAngularCollar_measurePreserving l r)).trans
  exact (sourceAngularCollar_measurePreserving l r).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (sourceAngularCollarMeasure_le hlr hl hr) f)

lemma sourceAngularCollar_quasi {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Measure.QuasiMeasurePreserving (Function.uncurry sourceAngularCollar)
      (sourceCylinderMeasure l r) (sourcePhysicalCollarMeasure l r) := by
  refine ⟨continuous_uncurry_sourceAngularCollar.measurable,?_⟩
  rw [(sourceAngularCollar_measurePreserving l r).map_eq]
  exact Measure.absolutelyContinuous_of_le_smul (sourceAngularCollarMeasure_le hlr hl hr)

lemma sourceAngularCollar_coordinates_ae {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    ∀ᵐ y∂sourcePhysicalCollarMeasure l r,
      Function.uncurry sourceAngularCollar (sourcePhysicalCoordinates y)=y := by
  apply (sourceCollar_ae_iff hlr hl hr).mpr
  rw [←(sourceAngularCollar_measurePreserving l r).map_eq]
  apply (ae_map_iff continuous_uncurry_sourceAngularCollar.aemeasurable
    (measurableSet_eq_fun
      (continuous_uncurry_sourceAngularCollar.measurable.comp measurable_sourcePhysicalCoordinates)
      measurable_id)).mpr
  have ht : ∀ᵐ z∂sourceCylinderMeasure l r,z.1∈Ioc l r :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [ht] with z hz
  change Function.uncurry sourceAngularCollar (sourcePhysicalCoordinates
    (sourceAngularCollar z.1 z.2))=sourceAngularCollar z.1 z.2
  rw [sourcePhysicalCoordinates_angular ⟨hl.trans hz.1.le,hz.2.trans hr⟩]
  rfl

lemma sourceCylinderPullback_collarPullback {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (f : Lp ℂ 2 (sourceCylinderMeasure l r)) :
    sourceCylinderPullback hlr hl hr (sourceCollarPullback hlr hl hr f)=f := by
  apply Lp.ext
  have he := (sourceAngularCollar_quasi hlr hl hr).ae_eq_comp (sourceCollarPullback_ae hlr hl hr f)
  have ht : ∀ᵐ z∂sourceCylinderMeasure l r,z.1∈Ioc l r :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [sourceCylinderPullback_ae hlr hl hr (sourceCollarPullback hlr hl hr f),he,ht]
    with z hz he ht
  rw [hz,he]
  change f (sourcePhysicalCoordinates (sourceAngularCollar z.1 z.2))=f z
  rw [sourcePhysicalCoordinates_angular ⟨hl.trans ht.1.le,ht.2.trans hr⟩]

lemma sourceCollarPullback_cylinderPullback {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (f : Lp ℂ 2 (sourcePhysicalCollarMeasure l r)) :
    sourceCollarPullback hlr hl hr (sourceCylinderPullback hlr hl hr f)=f := by
  apply Lp.ext
  have he := sourceCollarPullback_ae_of_ae hlr hl hr (sourceCylinderPullback hlr hl hr f)
    (sourceCylinderPullback_ae hlr hl hr f)
  filter_upwards [he,sourceAngularCollar_coordinates_ae hlr hl hr] with y hy he
  simpa only [Function.comp_apply,he] using hy

def sourceCylinderPhysicalEquiv {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Lp ℂ 2 (sourceCylinderMeasure l r) ≃L[ℝ] Lp ℂ 2 (sourcePhysicalCollarMeasure l r) where
  toFun := sourceCollarPullback hlr hl hr
  invFun := sourceCylinderPullback hlr hl hr
  left_inv := sourceCylinderPullback_collarPullback hlr hl hr
  right_inv := sourceCollarPullback_cylinderPullback hlr hl hr
  map_add' := (sourceCollarPullback hlr hl hr).map_add
  map_smul' := (sourceCollarPullback hlr hl hr).map_smul
  continuous_toFun := (sourceCollarPullback hlr hl hr).continuous
  continuous_invFun := (sourceCylinderPullback hlr hl hr).continuous

end ScalarConductivity

end
end

end OAI
