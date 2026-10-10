import OAI.Geometry.NodalSets.Charts.FixedChartSeedSupport
import OAI.Geometry.NodalSets.Coefficients.PositiveSphereCorrection

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance exteriorCorrectedEquationLocalInst1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst2 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance exteriorCorrectedEquationLocalInst3 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst4 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance exteriorCorrectedEquationLocalInst5 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst6 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance exteriorCorrectedEquationLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance exteriorCorrectedEquationLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance exteriorCorrectedEquationLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance exteriorCorrectedEquationLocalInst10 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance exteriorCorrectedEquationLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.isTopologicalAddGroup
local instance exteriorCorrectedEquationLocalInst12 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance exteriorCorrectedEquationLocalInst13 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance exteriorCorrectedEquationLocalInst14 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

local instance exteriorCorrectedEquationLocalInst15 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance exteriorCorrectedEquationLocalInst16 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module

lemma ambientWeightedChartOperator_field_eq (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (rho : Base → ℝ) (u v : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (he : u =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] v) :
    ambientWeightedChartOperator A rho u p z = ambientWeightedChartOperator A rho v p z := by
  have he' := he.comp_tendsto (continuousAt_extChartAt_symm'' hz)
  have hder := he'.fderiv (𝕜 := ℝ)
  have hflux (i : Fin 4) : roundTensorFlux A u p i =ᶠ[𝓝 z] roundTensorFlux A v p i := by
    filter_upwards [hder] with y hy
    simp only [roundTensorFlux]
    rw [hy]
  unfold ambientWeightedChartOperator
  congr 2
  funext i
  rw [(hflux i).fderiv_eq]

theorem corrected_exterior_equation (A : IntrinsicTensor) (rho : Base → ℝ)
    {K L : Set Base} (hK : IsClosed K) (hL : IsClosed L)
    (hA : ∀ x ∉ K, ∀ v w : AmbientBase,
      ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫)
    (hr : ∀ x ∉ K, rho x = 1) (a b u : Base → ℝ) (n : ℕ)
    (ha : tsupport a ⊆ L) (hb : tsupport b ⊆ L) (hu : tsupport (u-sphericalSeed n) ⊆ L)
    (p : Base) (z : BaseModel) (hz : (extChartAt (𝓡 4) p).symm z ∉ K ∪ L) :
    -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation a x)
      (fun x ↦ rho x+b x) u p z = seedEigenvalue n*u ((extChartAt (𝓡 4) p).symm z) := by
  have hAe (x : Base) (hx : x ∉ K ∪ L) :
      intrinsicAmbientMatrix (fun y ↦ A y+roundTensorPerturbation a y) x = 1 := by
    apply intrinsicAmbientMatrix_reference
    intro v w hv hw
    have hax : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (Or.inr (ha h)))
    change A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)+
      a x*roundCotangentTensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = _
    rw [hax,zero_mul,add_zero]
    exact hA x (fun h ↦ hx (Or.inl h)) v w hv hw
  have hre (x : Base) (hx : x ∉ K ∪ L) : rho x+b x = 1 := by
    rw [hr x (fun h ↦ hx (Or.inl h)),
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (Or.inr (hb h))),add_zero]
  have hgerm : u =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] sphericalSeed n := by
    have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (Or.inr (hu h)))
    filter_upwards [hzero] with y hy
    exact sub_eq_zero.mp hy
  have he := ambient_seed_fixed_chart_residual_zero
    (intrinsicAmbientMatrix (fun x ↦ A x+roundTensorPerturbation a x)) (fun x ↦ rho x+b x)
    (hK.union hL) hAe hre n p z hz
  rw [intrinsicWeightedChartOperator_eq,
    ambientWeightedChartOperator_field_eq _ _ u (sphericalSeed n) p
      (by rw [centeredSphereChart_target]; trivial) hgerm,hgerm.eq_of_nhds]
  linarith

end
end Yau.Target

end OAI
