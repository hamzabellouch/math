import OAI.Geometry.NodalSets.Charts.GlobalSphereEquation
import OAI.Geometry.NodalSets.Charts.IntrinsicCorrectedChart
import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientIncrementBounds

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsicWeightedChartOperator_coefficients_eq (A B : IntrinsicTensor)
    (rho sigma u : Base → ℝ) (p : Base) (z : BaseModel)
    (hA : ∀ᶠ x in 𝓝 ((extChartAt (𝓡 4) p).symm z), A x = B x)
    (hr : rho =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] sigma) :
    intrinsicWeightedChartOperator A rho u p z = intrinsicWeightedChartOperator B sigma u p z := by
  have he := (continuousAt_extChartAt_symm''
    (by rw [centeredSphereChart_target]; trivial : z ∈ (extChartAt (𝓡 4) p).target)).eventually hA
  have hf (i : Fin 4) : intrinsicRoundFlux A u p i =ᶠ[𝓝 z] intrinsicRoundFlux B u p i := by
    filter_upwards [he] with y hy
    simp only [intrinsicRoundFlux,intrinsicSphereChartTensor,hy]
  simp only [intrinsicWeightedChartOperator,hr.eq_of_nhds]
  congr 2
  funext i
  rw [(hf i).fderiv_eq]

lemma intrinsic_eigenfunction_correction_residual_zero
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho u : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z)) :
    ∀ x, intrinsicRealCorrectionResidual A rho lam (fun y ↦ u (seedSphereFromCoord y)) x = 0 := by
  intro x
  have hres := intrinsicRealCorrectionResidual_divergence A hA hs hp rho hrp u hu lam x
  change intrinsicRealCorrectionResidual A rho lam (fun y ↦ u (seedSphereFromCoord y)) x = _ at hres
  rw [hres]
  have hn : rho (seedSphereFromCoord x) ≠ 0 := (hrp _).ne'
  have h := congrArg (fun v : ℝ ↦ rho (seedSphereFromCoord x)*v) (he seedPoint (seedCoordEquiv x))
  change rho (seedSphereFromCoord x)*
    (-((rho (seedSphereFromCoord x))⁻¹*(roundCoordDensity x)⁻¹*
      (∑ i, fderiv ℝ (intrinsicRoundFlux A u seedPoint i) (seedCoordEquiv x)
        (EuclideanSpace.basisFun (Fin 4) ℝ i)))) =
      rho (seedSphereFromCoord x)*(lam*u (seedSphereFromCoord x)) at h
  simp only [← mul_assoc,mul_neg,mul_inv_cancel₀ hn,one_mul] at h
  change -(roundCoordDensity x)⁻¹ * _ - lam*rho (seedSphereFromCoord x)*u (seedSphereFromCoord x) = 0
  nlinarith only [h]

lemma round_preserving_cancellation_smul (u a b : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (lam t : ℝ)
    (he : ∀ x, Yau.weightedDiv roundCoordDensity
      (fun y i ↦ a (seedSphereFromCoord y)*roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i) x +
      lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) = 0) :
    ∀ x, Yau.weightedDiv roundCoordDensity
      (fun y i ↦ (t*a (seedSphereFromCoord y))*roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i) x +
      lam*(t*b (seedSphereFromCoord x))*u (seedSphereFromCoord x) = 0 := by
  intro x
  have hav := seed_scalar_pullback_smooth a ha
  have hV := roundCoordGradient_smooth _ (seed_scalar_pullback_smooth u hu)
  have hmul := Yau.weightedDiv_mul (gamma := roundCoordDensity) (u := fun _ ↦ t)
    (V := fun y i ↦ a (seedSphereFromCoord y)*roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i)
    (x := x) (roundCoordDensity_smooth.differentiable (by simp) x) (roundCoordDensity_pos x).ne'
    (differentiableAt_const t) (fun i ↦ (hav.mul ((contDiff_pi.mp hV) i)).differentiable (by simp) x)
  simp only [Yau.pairing,Yau.coordPartial,fderiv_fun_const,Pi.zero_apply,zero_apply,
    zero_mul,Finset.sum_const_zero,add_zero] at hmul
  simp only [mul_assoc] at ⊢ hmul
  rw [hmul]
  have ht := congrArg (fun q : ℝ ↦ t*q) (he x)
  nlinarith only [ht]

theorem sphere_equation_preserved_by_round_cancellation
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho u a b : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z))
    (hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation a x))
    (hnewSym : ∀ x v w, (A x+roundTensorPerturbation a x) v w = (A x+roundTensorPerturbation a x) w v)
    (hnewPos : ∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation a x) v v)
    (hrnew : ∀ x, 0 < rho x+b x)
    (hsa : tsupport a ⊆ (extChartAt (𝓡 4) seedPoint).source)
    (hsb : tsupport b ⊆ (extChartAt (𝓡 4) seedPoint).source)
    (hcancel : ∀ x, Yau.weightedDiv roundCoordDensity
      (fun y i ↦ a (seedSphereFromCoord y)*roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i) x +
      lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) = 0) :
    ∀ p z, -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation a x)
      (fun x ↦ rho x+b x) u p z = lam*u ((extChartAt (𝓡 4) p).symm z) := by
  have hres := intrinsic_eigenfunction_correction_residual_zero A hA hs hp rho u hrp hu lam he
  have hseed := corrected_seed_chart_equation A hA hs hp rho hrp u hu lam a b
    hnew hnewSym hnewPos hrnew (fun x ↦ (hcancel x).trans (hres x).symm)
  apply intrinsic_global_equation_of_seed_exterior _ hnew hnewSym hnewPos _ u hu lam
    (tsupport a ∪ tsupport b) (union_subset hsa hsb) hseed
  intro p z hz
  have ha0 := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (Or.inl h))
  have hb0 := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (Or.inr h))
  have hAe : ∀ᶠ x in 𝓝 ((extChartAt (𝓡 4) p).symm z),
      A x+roundTensorPerturbation a x = A x := by
    filter_upwards [ha0] with x hx
    simp [roundTensorPerturbation,hx]
  have hre : (fun x ↦ rho x+b x) =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] rho := by
    filter_upwards [hb0] with x hx
    simp [hx]
  rw [intrinsicWeightedChartOperator_coefficients_eq _ A _ rho u p z hAe hre]
  exact he p z

end
end Yau.Target

end OAI
