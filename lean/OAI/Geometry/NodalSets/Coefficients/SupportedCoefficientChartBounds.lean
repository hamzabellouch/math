import OAI.Geometry.NodalSets.Charts.SupportedSphereChartBounds
import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientIncrementBounds

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma roundTensorPerturbation_any_entry (a : Base → ℝ) (p : Base) (x : Yau.Jets.Coord) (j k : Fin 4) :
    intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv x) j k =
      if j=k then roundCoordFactor x*a (sphereChartCoordMap p x) else 0 := by
  rw [roundTensorPerturbation_chart,sphereRoundChartMatrix_inverse_conformal]
  have hfac : (((4:ℝ)/(‖seedCoordEquiv x‖^2+4))^2)⁻¹ = roundCoordFactor x := by
    unfold roundCoordFactor
    field_simp
  rw [hfac]
  simp [Matrix.one_apply,sphereChartCoordMap,mul_comm]

lemma round_increment_any_entry_smooth (a : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (p : Base) (j k : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv x) j k) := by
  simp_rw [roundTensorPerturbation_any_entry]
  split_ifs
  · exact roundCoordFactor_smooth.mul (ha.comp (sphereChartCoordMap_smooth p)).contDiff
  · exact contDiff_const

lemma intrinsic_any_increment_pullback_smooth (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (p : Base) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicChartCoefficient (roundTensorPerturbation a) b p (seedCoordEquiv x)) := by
  apply ContDiff.prodMk _ (hb.comp (sphereChartCoordMap_smooth p)).contDiff
  change ContDiff ℝ ∞ (fun x ↦ matrixContravariant
    (intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv x)))
  simp_rw [matrixContravariant_entry_sum]
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  exact ContDiff.sum (fun j _ ↦ ContDiff.sum (fun k _ ↦
    (round_increment_any_entry_smooth a ha p j k).smul contDiff_const))

theorem supported_sphere_coefficient_coord_bound (r : ℝ) (p : Base)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (J : ℕ) :
    ∃ C > 0, ∀ (A : IntrinsicTensor) (rho a b : Base → ℝ),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b →
      tsupport a ⊆ seedSpherePatch r → tsupport b ⊆ seedSpherePatch r →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ a (seedSphereFromCoord y)) x‖ ≤ eps) →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ b (seedSphereFromCoord y)) x‖ ≤ eps) →
      ∀ x ∈ Q, ∀ i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦
        intrinsicChartCoefficient (fun z ↦ A z+roundTensorPerturbation a z)
          (fun z ↦ rho z+b z) p (seedCoordEquiv y)-intrinsicChartCoefficient A rho p (seedCoordEquiv y)) x‖ ≤ C*eps := by
  obtain ⟨Cs,hCs,hscalar⟩ := supported_sphere_chart_scalar_bound r p hQ J
  obtain ⟨Cm,hCm,hmul⟩ := compact_multiplier_frequency_bound roundCoordFactor roundCoordFactor_smooth hQ J
  let K : ℝ := 1+∑ j, ∑ k, ‖coefficientEntryLinear j k‖
  have hK : 0 < K := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦
      Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) ↦ norm_nonneg (coefficientEntryLinear j k)))
    dsimp [K]; linarith
  refine ⟨K*((Cm+1)*Cs),by positivity,?_⟩
  intro A rho a b ha hb has hbs eps heps hab hbb x hx i hi
  have ha' := hscalar a ha has eps heps hab
  have hb' := hscalar b hb hbs eps heps hbb
  have hm (j k : Fin 4) : ‖iteratedFDeriv ℝ i (fun y ↦
      intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv y) j k) x‖ ≤ ((Cm+1)*Cs)*eps := by
    simp_rw [roundTensorPerturbation_any_entry]
    by_cases hjk : j=k
    · simp only [hjk,ite_true]
      have h := hmul (fun y ↦ a (sphereChartCoordMap p y))
        (ha.comp (sphereChartCoordMap_smooth p)).contDiff 1 (Cs*eps) (by norm_num) (by positivity) 0 x hx
        (fun k hk ↦ by simpa using ha' x hx k hk) i hi
      simp only [one_pow,mul_one] at h
      exact h.trans (by nlinarith)
    · simp only [hjk,ite_false]
      simpa using (show 0 ≤ ((Cm+1)*Cs)*eps by positivity)
  have hbnd : ‖iteratedFDeriv ℝ i (fun y ↦ b (sphereChartCoordMap p y)) x‖ ≤ ((Cm+1)*Cs)*eps :=
    (hb' x hx i hi).trans (by nlinarith [mul_nonneg hCm.le (mul_nonneg hCs.le heps)])
  simp_rw [intrinsicChartCoefficient_increment]
  have h := matrix_coefficient_derivative_bound _ _ (round_increment_any_entry_smooth a ha p)
    (hb.comp (sphereChartCoordMap_smooth p)).contDiff x i (by positivity) hm hbnd
  simpa only [K,intrinsicChartCoefficient,sphereChartCoordMap,Function.comp_def,mul_assoc] using h

theorem supported_sphere_coefficient_bound (r : ℝ) (p : Base)
    {Q : Set BaseModel} (hQ : IsCompact Q) (J : ℕ) :
    ∃ C > 0, ∀ (A : IntrinsicTensor) (rho a b : Base → ℝ),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b →
      tsupport a ⊆ seedSpherePatch r → tsupport b ⊆ seedSpherePatch r →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ a (seedSphereFromCoord y)) x‖ ≤ eps) →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ b (seedSphereFromCoord y)) x‖ ≤ eps) →
      ∀ z ∈ Q, ∀ i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦
        intrinsicChartCoefficient (fun x ↦ A x+roundTensorPerturbation a x)
          (fun x ↦ rho x+b x) p y-intrinsicChartCoefficient A rho p y) z‖ ≤ C*eps := by
  obtain ⟨C,hC,hcoord⟩ := supported_sphere_coefficient_coord_bound r p
    (hQ.image seedCoordEquiv.symm.continuous) J
  let B : ℝ := max 1 ‖seedCoordEquiv.symm.toContinuousLinearMap‖
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨C*B^J,by positivity,?_⟩
  intro A rho a b ha hb has hbs eps heps hab hbb z hz i hi
  let F : Yau.Jets.Coord → CoefficientPoint BaseModel := fun x ↦
    intrinsicChartCoefficient (roundTensorPerturbation a) b p (seedCoordEquiv x)
  have hF : ContDiff ℝ ∞ F := intrinsic_any_increment_pullback_smooth a b ha hb p
  have hpoint : ‖iteratedFDeriv ℝ i F (seedCoordEquiv.symm z)‖ ≤ C*eps := by
    simpa only [intrinsicChartCoefficient_increment] using
      hcoord A rho a b ha hb has hbs eps heps hab hbb _ ⟨z,hz,rfl⟩ i hi
  simp_rw [intrinsicChartCoefficient_increment]
  have heq : intrinsicChartCoefficient (roundTensorPerturbation a) b p =
      F ∘ seedCoordEquiv.symm.toContinuousLinearMap := by funext y; simp [F]
  rw [heq,seedCoordEquiv.symm.toContinuousLinearMap.iteratedFDeriv_comp_right hF z
    (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hpow : ‖seedCoordEquiv.symm.toContinuousLinearMap‖^i ≤ B^J :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i).trans (pow_le_pow_right₀ hB hi)
  calc
    _ ≤ (C*eps)*B^J := mul_le_mul hpoint hpow (by positivity) (by positivity)
    _ = _ := by ring

end
end Yau.Target

end OAI
