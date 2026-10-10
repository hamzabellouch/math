import OAI.Geometry.NodalSets.Coefficients.PositiveSphereCorrection
import OAI.Geometry.NodalSets.Elliptic.RoundPerturbationFlux

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance intrinsicCorrectedChartLocalInst1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst2 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance intrinsicCorrectedChartLocalInst3 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst4 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicCorrectedChartLocalInst5 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst6 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicCorrectedChartLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance intrinsicCorrectedChartLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance intrinsicCorrectedChartLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicCorrectedChartLocalInst10 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance intrinsicCorrectedChartLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.isTopologicalAddGroup
local instance intrinsicCorrectedChartLocalInst12 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance intrinsicCorrectedChartLocalInst13 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance intrinsicCorrectedChartLocalInst14 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

local instance intrinsicCorrectedChartLocalInst15 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicCorrectedChartLocalInst16 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module

lemma intrinsicRoundFlux_add (A B : IntrinsicTensor) (f : Base → ℝ) (p : Base) (i : Fin 4) :
    intrinsicRoundFlux (fun x ↦ A x+B x) f p i =
      fun z ↦ intrinsicRoundFlux A f p i z+intrinsicRoundFlux B f p i z := by
  funext z
  simp only [intrinsicRoundFlux,intrinsicSphereChartTensor_add,Matrix.add_apply,
    add_mul,Finset.sum_add_distrib,mul_add]

theorem corrected_seed_chart_equation (A : IntrinsicTensor) (hAs : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ) (a b : Base → ℝ)
    (hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation a x))
    (hnewSym : ∀ x v w, (A x+roundTensorPerturbation a x) v w = (A x+roundTensorPerturbation a x) w v)
    (hnewPos : ∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation a x) v v)
    (hrnew : ∀ x, 0 < rho x+b x)
    (heq : ∀ x, Yau.weightedDiv roundCoordDensity
      (fun y i ↦ a (seedSphereFromCoord y)*roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i) x +
      lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) =
      intrinsicRealCorrectionResidual A rho lam (fun z ↦ u (seedSphereFromCoord z)) x) :
    ∀ x, -intrinsicWeightedChartOperator (fun p ↦ A p+roundTensorPerturbation a p)
      (fun p ↦ rho p+b p) u seedPoint (seedCoordEquiv x) = lam*u (seedSphereFromCoord x) := by
  intro x
  let B := roundTensorPerturbation a
  have hdiff (i : Fin 4) : Differentiable ℝ (intrinsicRoundFlux B u seedPoint i) := by
    have hn := intrinsicRoundFlux_smooth (fun p ↦ A p+B p) hnew hnewSym hnewPos u hu seedPoint i
    have ho := intrinsicRoundFlux_smooth A hAs hs hp u hu seedPoint i
    have he : intrinsicRoundFlux B u seedPoint i = fun z ↦
        intrinsicRoundFlux (fun p ↦ A p+B p) u seedPoint i z-intrinsicRoundFlux A u seedPoint i z := by
      funext z
      rw [intrinsicRoundFlux_add]
      ring
    rw [he]
    exact (hn.sub ho).differentiable (by simp)
  have hsum : (∑ i, fderiv ℝ (intrinsicRoundFlux (fun p ↦ A p+B p) u seedPoint i)
      (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i)) =
      (∑ i, fderiv ℝ (intrinsicRoundFlux A u seedPoint i)
        (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i)) +
      (∑ i, fderiv ℝ (intrinsicRoundFlux B u seedPoint i)
        (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i)) := by
    simp only [intrinsicRoundFlux_add]
    simp_rw [fderiv_fun_add
      ((intrinsicRoundFlux_smooth A hAs hs hp u hu seedPoint _).differentiable (by simp) _)
      (hdiff _ _),add_apply,Finset.sum_add_distrib]
  have h := heq x
  rw [← roundTensorPerturbation_seed_divergence] at h
  have hres := intrinsicRealCorrectionResidual_divergence A hAs hs hp rho hrp u hu lam x
  change intrinsicRealCorrectionResidual A rho lam (fun z ↦ u (seedSphereFromCoord z)) x = _ at hres
  rw [hres] at h
  change -((rho (seedSphereFromCoord x)+b (seedSphereFromCoord x))⁻¹ *
    (roundCoordDensity x)⁻¹ *
      (∑ i, fderiv ℝ (intrinsicRoundFlux (fun p ↦ A p+B p) u seedPoint i)
        (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i))) = _
  rw [hsum]
  have hd : rho (seedSphereFromCoord x)+b (seedSphereFromCoord x) ≠ 0 := (hrnew _).ne'
  change _ + lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) =
    _ - lam*rho (seedSphereFromCoord x)*u (seedSphereFromCoord x) at h
  apply (mul_left_cancel₀ hd)
  field_simp
  simp only [div_eq_mul_inv]
  dsimp only [B] at *
  nlinarith only [h]

end
end Yau.Target

end OAI
