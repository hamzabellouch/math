import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicMeasure

namespace OAI

/-! The already computed hyperbolic Jacobian also applies to the
nonintegral prime normalizer on the same positive-height space. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

instance cubicThetaComplexPointAction_continuous : ContinuousConstSMul SL(2,ℂ) CubicThetaPoint where
  continuous_const_smul g := by
    change Continuous (fun x : CubicThetaPoint =>
      (⟨cubicThetaMobius g x.val,cubicThetaMobius_height_pos _ x.property⟩ : CubicThetaPoint))
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (cubicThetaMobius_continuousAt g x.property).comp
      (x:=x) (f:=fun y : CubicThetaPoint => y.val) continuous_subtype_val.continuousAt

lemma cubicThetaComplexPointMeasure_image (g : SL(2,ℂ)) {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) :
    cubicThetaPointMeasure ((fun x => g • x) '' S)=cubicThetaPointMeasure S := by
  have hI : MeasurableSet ((fun x : CubicThetaPoint => g • x) '' S) :=
    (Homeomorph.smul g).measurableEmbedding.measurableSet_image' hS
  rw [cubicThetaPointMeasure_apply hI,cubicThetaPointMeasure_apply hS]
  have he : cubicThetaPointCoordinates '' ((fun x : CubicThetaPoint => g • x) '' S)=
      cubicThetaMobius g '' (cubicThetaPointCoordinates '' S) := by
    rw [image_image,image_image]
    rfl
  rw [he]
  apply cubicThetaHyperbolicMeasure_image _
    (cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS)
  rintro x ⟨y,_,rfl⟩
  exact y.property

instance cubicThetaComplexPointMeasure_invariant :
    SMulInvariantMeasure SL(2,ℂ) CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g S hS := by
    have he : (fun x : CubicThetaPoint => g • x) ⁻¹' S=(fun x => g⁻¹ • x) '' S := by
      ext x
      constructor
      · intro hx
        exact ⟨g • x,hx,inv_smul_smul g x⟩
      · rintro ⟨y,hy,rfl⟩
        change g • (g⁻¹ • y)∈S
        rwa [smul_inv_smul]
    rw [he]
    exact cubicThetaComplexPointMeasure_image g⁻¹ hS

end CubicFirstMoment

end

end OAI
