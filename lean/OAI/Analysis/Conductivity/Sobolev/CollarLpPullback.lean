import Mathlib
import OAI.Analysis.Conductivity.Branching.CollarMeasureTransport
import OAI.Analysis.Conductivity.Fourier.CollarAngularInverse

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

abbrev sourceCylinderMeasure (l r : ℝ) : Measure (ℝ×UnitAddTorus (Fin 2)) :=
  (volume.restrict (Ioc l r)).prod
    (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))

lemma sourceCylinderMeasure_eq (l r : ℝ) : sourceCylinderMeasure l r =
    (volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2))) := by
  apply congrArg (Measure.prod (volume.restrict (Ioc l r)))
  change Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)=
    Measure.pi (fun _ : Fin 2 => (volume : Measure UnitAddCircle))
  simp_rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

def sourcePhysicalCoordinates (y : Fin 3 → ℝ) : ℝ×UnitAddTorus (Fin 2) :=
  (sourceCollarTime y,sourcePhysicalAngles y)

lemma measurable_sourcePhysicalCoordinates : Measurable sourcePhysicalCoordinates := by
  have ht : Continuous sourceCollarTime := by
    unfold sourceCollarTime sourceCrossCoordinates sourceRadial
    fun_prop
  exact ht.measurable.prodMk measurable_sourcePhysicalAngles

lemma sourcePhysicalCoordinates_angular {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) :
    sourcePhysicalCoordinates (sourceAngularCollar t θ)=(t,θ) := by
  exact Prod.ext (sourceAngular_time ht θ) (sourcePhysicalAngles_angular ht θ)

lemma sourcePhysicalCoordinates_measurePreserving {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    MeasurePreserving sourcePhysicalCoordinates (sourceAngularCollarMeasure l r)
      (sourceCylinderMeasure l r) := by
  refine ⟨measurable_sourcePhysicalCoordinates,?_⟩
  unfold sourceAngularCollarMeasure
  rw [←sourceCylinderMeasure_eq]
  rw [Measure.map_map measurable_sourcePhysicalCoordinates continuous_uncurry_sourceAngularCollar.measurable]
  have he : sourcePhysicalCoordinates ∘ Function.uncurry sourceAngularCollar=ᵐ[sourceCylinderMeasure l r] id := by
    have ht : ∀ᵐ z∂sourceCylinderMeasure l r,z.1∈Ioc l r :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [ht] with z hz
    exact sourcePhysicalCoordinates_angular ⟨hl.trans hz.1.le,hz.2.trans hr⟩ z.2
  rw [Measure.map_congr he,Measure.map_id]

def sourceCollarPullback {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Lp ℂ 2 (sourceCylinderMeasure l r) →L[ℝ]
      Lp ℂ 2 (sourcePhysicalCollarMeasure l r) :=
  (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (sourcePhysicalCollarMeasure_le hlr hl hr)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ sourcePhysicalCoordinates
      (sourcePhysicalCoordinates_measurePreserving hl hr)).toContinuousLinearMap

lemma sourceCollarPullback_ae {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (f : Lp ℂ 2 (sourceCylinderMeasure l r)) :
    sourceCollarPullback hlr hl hr f=ᵐ[sourcePhysicalCollarMeasure l r]
      f ∘ sourcePhysicalCoordinates := by
  have h0 := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (sourcePhysicalCollarMeasure_le hlr hl hr)
    ((Lp.compMeasurePreservingₗᵢ ℝ sourcePhysicalCoordinates
      (sourcePhysicalCoordinates_measurePreserving hl hr)) f)
  have h1 := Lp.coeFn_compMeasurePreserving f (sourcePhysicalCoordinates_measurePreserving hl hr)
  exact h0.trans ((Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalCollarMeasure_le hlr hl hr)).ae_eq h1)

lemma sourceCollarPullback_ae_of_ae {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (f : Lp ℂ 2 (sourceCylinderMeasure l r))
    {g : (ℝ×UnitAddTorus (Fin 2)) → ℂ} (hg : f=ᵐ[sourceCylinderMeasure l r] g) :
    sourceCollarPullback hlr hl hr f=ᵐ[sourcePhysicalCollarMeasure l r]
      g ∘ sourcePhysicalCoordinates := by
  apply (sourceCollarPullback_ae hlr hl hr f).trans
  exact (Measure.absolutelyContinuous_of_le_smul (sourcePhysicalCollarMeasure_le hlr hl hr)).ae_eq
    ((sourcePhysicalCoordinates_measurePreserving hl hr).quasiMeasurePreserving.ae_eq_comp hg)

lemma sourceCollarPullback_hasSum {l r : ℝ} (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {ι : Type*}
    {F : ι → Lp ℂ 2 (sourceCylinderMeasure l r)} {f : Lp ℂ 2 (sourceCylinderMeasure l r)}
    (hf : HasSum F f) :
    HasSum (fun i => sourceCollarPullback hlr hl hr (F i))
      (sourceCollarPullback hlr hl hr f) :=
  (sourceCollarPullback hlr hl hr).hasSum hf

end ScalarConductivity

end

end OAI
