import OAI.Geometry.NodalSets.Charts.RoundCotangentTensor
import OAI.Geometry.NodalSets.Charts.SmoothBundleInverse
import OAI.Geometry.NodalSets.Elliptic.IntrinsicAmbientSmooth

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance roundCotangentSmoothLocalInst1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
local instance roundCotangentSmoothLocalInst2 (x : Base) : NormedAddCommGroup (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedAddCommGroup BaseModel)
local instance roundCotangentSmoothLocalInst3 (x : Base) : NormedSpace ℝ (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedSpace ℝ BaseModel)
local instance roundCotangentSmoothLocalInst4 (x : Base) : FiniteDimensional ℝ (TangentSpace (𝓡 4) x) := inferInstanceAs (FiniteDimensional ℝ BaseModel)

lemma sphereRoundMusical_smooth :
    ContMDiff (𝓡 4) ((𝓡 4).prod 𝓘(ℝ,BaseModel →L[ℝ] CotangentModel)) ∞
      (fun x ↦ TotalSpace.mk' (BaseModel →L[ℝ] CotangentModel)
        (E := fun x ↦ TangentSpace (𝓡 4) x →L[ℝ] SphereCotangent x) x
        (sphereRoundMusical x).toContinuousLinearMap) := by
  exact smooth_bilinear_pullback (fun _ ↦ innerSL ℝ) sphereAmbientDerivative contMDiff_const
    (smooth_ambient_derivative (Subtype.val : Base → AmbientBase) (contMDiff_coe_sphere (n := 4)))

lemma sphereRoundMusical_inverse_smooth :
    ContMDiff (𝓡 4) ((𝓡 4).prod 𝓘(ℝ,CotangentModel →L[ℝ] BaseModel)) ∞
      (fun x ↦ TotalSpace.mk' (CotangentModel →L[ℝ] BaseModel)
        (E := fun x ↦ SphereCotangent x →L[ℝ] TangentSpace (𝓡 4) x) x
        (sphereRoundMusical x).symm.toContinuousLinearMap) :=
  smooth_bundle_inverse sphereRoundMusical sphereRoundMusical_smooth

local instance : ContinuousSMul ℝ AmbientBase := IsBoundedSMul.continuousSMul

lemma sphereCotangentRepresentative_smooth :
    ContMDiff (𝓡 4) ((𝓡 4).prod 𝓘(ℝ,CotangentModel →L[ℝ] AmbientBase)) ∞
      (fun x ↦ TotalSpace.mk' (CotangentModel →L[ℝ] AmbientBase)
        (E := fun x ↦ SphereCotangent x →L[ℝ] Bundle.Trivial Base AmbientBase x) x
        (sphereCotangentRepresentative x)) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id,?_⟩
  have ht := ((contMDiffAt_hom_bundle _).mp (sphereRoundMusical_inverse_smooth x)).2
  have hd := ((contMDiffAt_hom_bundle _).mp
    (smooth_ambient_derivative (Subtype.val : Base → AmbientBase)
      (contMDiff_coe_sphere (n := 4)) x)).2
  change ContMDiffAt (𝓡 4) 𝓘(ℝ,BaseModel →L[ℝ] AmbientBase) ∞
    (fun y ↦ inCoordinates BaseModel (TangentSpace (𝓡 4)) AmbientBase
      (Bundle.Trivial Base AmbientBase) x y x y (sphereAmbientDerivative y)) x at hd
  apply (hd.clm_comp ht).congr_of_eventuallyEq
  filter_upwards [(trivializationAt BaseModel (TangentSpace (𝓡 4)) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt BaseModel (TangentSpace (𝓡 4)) x),
    (trivializationAt CotangentModel SphereCotangent x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt CotangentModel SphereCotangent x)] with y hy hz
  have hw : y ∈ (trivializationAt AmbientBase (Bundle.Trivial Base AmbientBase) x).baseSet := Set.mem_univ y
  simp only [inCoordinates_eq hy hw,inCoordinates_eq hz hy,inCoordinates_eq hz hw]
  apply ContinuousLinearMap.ext
  intro v
  let e := (trivializationAt BaseModel (TangentSpace (𝓡 4)) x).continuousLinearEquivAt ℝ y hy
  let u : TangentSpace (𝓡 4) y := (sphereRoundMusical y).symm
    ((trivializationAt CotangentModel SphereCotangent x).symm y v)
  change sphereAmbientDerivative y u = sphereAmbientDerivative y (e.symm (e u))
  exact congrArg (sphereAmbientDerivative y) (e.symm_apply_apply u).symm

lemma roundCotangentTensor_smooth : IntrinsicTensorSmooth roundCotangentTensor := by
  exact smooth_bilinear_pullback (fun _ ↦ innerSL ℝ) sphereCotangentRepresentative
    contMDiff_const sphereCotangentRepresentative_smooth

end
end Yau.Target

end OAI
