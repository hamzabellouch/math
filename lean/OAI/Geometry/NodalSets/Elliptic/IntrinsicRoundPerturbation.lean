import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import OAI.Geometry.NodalSets.Charts.IntrinsicChartTensor
import OAI.Geometry.NodalSets.Charts.RoundCotangentSmooth
import OAI.Geometry.NodalSets.Charts.SphereChartConformal

namespace OAI

namespace Yau.Target
open Bundle Manifold Matrix Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance intrinsicRoundPerturbationLocalInst1 (x : Base) : NormedAddCommGroup (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedAddCommGroup BaseModel)
local instance intrinsicRoundPerturbationLocalInst2 (x : Base) : NormedSpace ℝ (TangentSpace (𝓡 4) x) := inferInstanceAs (NormedSpace ℝ BaseModel)

local instance intrinsicRoundPerturbationLocalInst3 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicRoundPerturbationLocalInst4 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance intrinsicRoundPerturbationLocalInst5 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicRoundPerturbationLocalInst6 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicRoundPerturbationLocalInst7 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicRoundPerturbationLocalInst8 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicRoundPerturbationLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance intrinsicRoundPerturbationLocalInst10 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance intrinsicRoundPerturbationLocalInst11 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicRoundPerturbationLocalInst12 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance intrinsicRoundPerturbationLocalInst13 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.isTopologicalAddGroup
local instance intrinsicRoundPerturbationLocalInst14 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance intrinsicRoundPerturbationLocalInst15 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance intrinsicRoundPerturbationLocalInst16 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

local instance intrinsicRoundPerturbationLocalInst17 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicRoundPerturbationLocalInst18 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module

def roundTensorPerturbation (alpha : Base → ℝ) : IntrinsicTensor :=
  fun x ↦ alpha x • roundCotangentTensor x

lemma roundTensorPerturbation_smooth (alpha : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ alpha) :
    IntrinsicTensorSmooth (roundTensorPerturbation alpha) :=
  ha.smul_section roundCotangentTensor_smooth

lemma roundTensorPerturbation_apply (alpha : Base → ℝ) (x : Base) (v w : SphereCotangent x) :
    roundTensorPerturbation alpha x v w = alpha x * roundCotangentTensor x v w := rfl

lemma roundTensorPerturbation_zero (alpha : Base → ℝ) (x : Base) (hx : x ∉ tsupport alpha) :
    roundTensorPerturbation alpha x = 0 := by
  ext v w
  simp [roundTensorPerturbation,image_eq_zero_of_notMem_tsupport hx]

lemma roundTensorPerturbation_tangent (alpha : Base → ℝ) (x : Base) (v w : AmbientBase)
    (hv : ⟪(x:AmbientBase),v⟫ = 0) (hw : ⟪(x:AmbientBase),w⟫ = 0) :
    roundTensorPerturbation alpha x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) =
      alpha x * ⟪v,w⟫ := by
  rw [roundTensorPerturbation_apply,roundCotangentTensor_tangent x v w hv hw]

lemma intrinsicSphereChartTensor_add (A B : IntrinsicTensor) (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor (fun x ↦ A x+B x) p z =
      intrinsicSphereChartTensor A p z+intrinsicSphereChartTensor B p z := by
  ext i j
  rfl

lemma roundCotangentTensor_chart (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor roundCotangentTensor p z = (sphereRoundChartMatrix p z)⁻¹ := by
  rw [intrinsicSphereChartTensor_eq]
  have he : intrinsicAmbientMatrix roundCotangentTensor = fun _ ↦ 1 := funext roundCotangentTensor_ambient
  rw [he]
  have hinv := Matrix.mul_nonsing_inv (sphereRoundChartMatrix p z)
    (isUnit_iff_ne_zero.mpr (sphereRoundChartMatrix_posDef p
      (by rw [centeredSphereChart_target]; trivial)).det_pos.ne')
  simp only [sphereChartTensor,frameContravariant,Matrix.mul_one]
  simp only [Matrix.mul_assoc] at *
  rw [← Matrix.mul_assoc (sphereChartFrame p z).transpose (sphereChartFrame p z)]
  change (sphereRoundChartMatrix p z)⁻¹ * (sphereRoundChartMatrix p z * (sphereRoundChartMatrix p z)⁻¹) = _
  rw [hinv,Matrix.mul_one]

lemma roundTensorPerturbation_chart (alpha : Base → ℝ) (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor (roundTensorPerturbation alpha) p z =
      alpha ((extChartAt (𝓡 4) p).symm z) • (sphereRoundChartMatrix p z)⁻¹ := by
  rw [← roundCotangentTensor_chart]
  ext i j
  rfl

end
end Yau.Target

end OAI
