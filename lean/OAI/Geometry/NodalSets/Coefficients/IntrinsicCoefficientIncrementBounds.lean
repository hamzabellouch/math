import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientMap
import OAI.Geometry.NodalSets.Coefficients.MatrixCoefficientBounds
import OAI.Geometry.NodalSets.Elliptic.RoundTensorCoordinateBounds

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsicChartCoefficient_increment (A B : IntrinsicTensor) (rho b : Base → ℝ)
    (p : Base) (z : BaseModel) :
    intrinsicChartCoefficient (fun x ↦ A x+B x) (fun x ↦ rho x+b x) p z -
      intrinsicChartCoefficient A rho p z = intrinsicChartCoefficient B b p z := by
  apply Prod.ext
  · simp only [intrinsicChartCoefficient,Prod.fst_sub,intrinsicSphereChartTensor_add,
      matrixContravariant_add,add_sub_cancel_left]
  · simp [intrinsicChartCoefficient]

lemma seed_scalar_pullback_smooth (b : Base → ℝ)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) :
    ContDiff ℝ ∞ (fun x ↦ b (seedSphereFromCoord x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (smooth_inverse_chart_comp b hb seedPoint
    (by rw [centeredSphereChart_target]; trivial)).comp x seedCoordEquiv.contDiff.contDiffAt

lemma round_increment_entry_smooth (a : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (j k : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicSphereChartTensor (roundTensorPerturbation a)
      seedPoint (seedCoordEquiv x) j k) := by
  simp_rw [roundTensorPerturbation_seed_entry]
  split_ifs
  · exact roundCoordFactor_smooth.mul (seed_scalar_pullback_smooth a ha)
  · exact contDiff_const

lemma intrinsic_seed_increment_pullback_smooth (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicChartCoefficient (roundTensorPerturbation a) b
      seedPoint (seedCoordEquiv x)) := by
  apply ContDiff.prodMk _ (seed_scalar_pullback_smooth b hb)
  change ContDiff ℝ ∞ (fun x ↦ matrixContravariant
    (intrinsicSphereChartTensor (roundTensorPerturbation a) seedPoint (seedCoordEquiv x)))
  simp_rw [matrixContravariant_entry_sum]
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  exact ContDiff.sum (fun j _ ↦ ContDiff.sum (fun k _ ↦
    (round_increment_entry_smooth a ha j k).smul contDiff_const))

lemma intrinsic_seed_increment_smooth (A : IntrinsicTensor) (rho a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) :
    ContDiff ℝ ∞ (fun z ↦
      intrinsicChartCoefficient (fun p ↦ A p+roundTensorPerturbation a p)
        (fun p ↦ rho p+b p) seedPoint z-intrinsicChartCoefficient A rho seedPoint z) := by
  simp_rw [intrinsicChartCoefficient_increment]
  have h := (intrinsic_seed_increment_pullback_smooth a b ha hb).comp seedCoordEquiv.symm.contDiff
  simpa only [Function.comp_def,ContinuousLinearEquiv.apply_symm_apply] using h

theorem intrinsic_coefficient_increment_derivative_bound (J : ℕ) :
    ∃ C > 0, ∀ (A : IntrinsicTensor) (rho a b : Base → ℝ),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ b (seedSphereFromCoord y)) x‖ ≤ eps) →
      (∀ x i j k, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦
        intrinsicSphereChartTensor (roundTensorPerturbation a) seedPoint (seedCoordEquiv y) j k) x‖ ≤ eps) →
      ∀ z i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦
        intrinsicChartCoefficient (fun p ↦ A p+roundTensorPerturbation a p)
          (fun p ↦ rho p+b p) seedPoint y-intrinsicChartCoefficient A rho seedPoint y) z‖ ≤ C*eps := by
  let K : ℝ := 1+∑ j, ∑ k, ‖coefficientEntryLinear j k‖
  let B : ℝ := max 1 ‖seedCoordEquiv.symm.toContinuousLinearMap‖
  have hK : 0 < K := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦
      Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) ↦ norm_nonneg (coefficientEntryLinear j k)))
    dsimp [K]; linarith
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨K*B^J,by positivity,?_⟩
  intro A rho a b ha hb eps heps hbb hab z i hi
  let F : Yau.Jets.Coord → CoefficientPoint BaseModel := fun x ↦
    intrinsicChartCoefficient (roundTensorPerturbation a) b seedPoint (seedCoordEquiv x)
  have hF : ContDiff ℝ ∞ F := intrinsic_seed_increment_pullback_smooth a b ha hb
  have hpoint : ‖iteratedFDeriv ℝ i F (seedCoordEquiv.symm z)‖ ≤ K*eps :=
    matrix_coefficient_derivative_bound _ _ (round_increment_entry_smooth a ha)
      (seed_scalar_pullback_smooth b hb) _ i heps
      (fun j k ↦ hab _ i j k hi) (hbb _ i hi)
  simp_rw [intrinsicChartCoefficient_increment]
  have heq : intrinsicChartCoefficient (roundTensorPerturbation a) b seedPoint =
      F ∘ seedCoordEquiv.symm.toContinuousLinearMap := by
    funext y
    simp [F]
  rw [heq,seedCoordEquiv.symm.toContinuousLinearMap.iteratedFDeriv_comp_right hF z (by exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top))]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hpow : ‖seedCoordEquiv.symm.toContinuousLinearMap‖^i ≤ B^J := by
    calc
      _ ≤ B^i := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
      _ ≤ B^J := pow_le_pow_right₀ hB hi
  calc
    _ ≤ (K*eps)*B^J := mul_le_mul hpoint hpow (by positivity) (by positivity)
    _ = (K*B^J)*eps := by ring

end
end Yau.Target

end OAI
