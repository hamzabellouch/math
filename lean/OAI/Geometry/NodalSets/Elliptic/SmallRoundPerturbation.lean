import OAI.Geometry.NodalSets.Coefficients.PositiveSphereCorrection
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientDistanceLaws

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsic_round_increment_smooth (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    (p : Base) : ContDiff ℝ ∞ (intrinsicChartCoefficient (roundTensorPerturbation a) b p) := by
  have h := (intrinsic_any_increment_pullback_smooth a b ha hb p).comp seedCoordEquiv.symm.contDiff
  simpa only [Function.comp_def,ContinuousLinearEquiv.apply_symm_apply] using h

lemma intrinsic_round_increment_smul (a b : Base → ℝ) (t : ℝ) (p : Base) (z : BaseModel) :
    intrinsicChartCoefficient (roundTensorPerturbation (fun x ↦ t*a x)) (fun x ↦ t*b x) p z =
      t • intrinsicChartCoefficient (roundTensorPerturbation a) b p z := by
  apply Prod.ext
  · change matrixContravariant (intrinsicSphereChartTensor
        (roundTensorPerturbation (fun x ↦ t*a x)) p z) =
      t • matrixContravariant (intrinsicSphereChartTensor (roundTensorPerturbation a) p z)
    simp only [roundTensorPerturbation_chart,matrixContravariant,Matrix.smul_apply,
      smul_eq_mul,Finset.smul_sum,smul_smul,mul_assoc]
  · rfl

lemma sphereCoefficientDistance_round_smul (P : Finset Base) (J : ℕ)
    (A : IntrinsicTensor) (rho a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (t : ℝ) :
    sphereCoefficientDistance P J A rho
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) (fun x ↦ rho x+t*b x) =
      |t| * finiteChartDerivativeSize P sphereAtlasCore J
        (intrinsicChartCoefficient (roundTensorPerturbation a) b) := by
  simp only [sphereCoefficientDistance,intrinsicChartCoefficient_increment,intrinsic_round_increment_smul]
  simpa only [Real.norm_eq_abs] using finiteChartDerivativeSize_smul P sphereAtlasCore_compact J t
    (intrinsicChartCoefficient (roundTensorPerturbation a) b)
    (fun p _ ↦ intrinsic_round_increment_smooth a b ha hb p)

theorem small_round_perturbation_in_finite_atlas
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (P : Finset Base) (J : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ t : ℝ, |t| < delta →
      IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) ∧
      (∀ x v w, (A x+roundTensorPerturbation (fun y ↦ t*a y) x) v w =
        (A x+roundTensorPerturbation (fun y ↦ t*a y) x) w v) ∧
      (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation (fun y ↦ t*a y) x) v v) ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+t*b x) ∧
      (∀ x, 0 < rho x+t*b x) ∧
      sphereCoefficientDistance P J A rho
        (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) (fun x ↦ rho x+t*b x) < eps := by
  obtain ⟨c,hc,hAm,hrm⟩ := intrinsic_pair_positive_margin A hA hs hp rho hr hrp
  obtain ⟨Ba,hBa⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuous.continuousOn
  obtain ⟨Bb,hBb⟩ := isCompact_univ.exists_bound_of_continuousOn hb.continuous.continuousOn
  let B : ℝ := max 0 (max Ba Bb)+1
  have hB : 0 < B := by dsimp [B]; have := le_max_left (0:ℝ) (max Ba Bb); linarith
  have hab (x : Base) : |a x| ≤ B := by
    have h := hBa x (mem_univ x)
    rw [Real.norm_eq_abs] at h
    have hh : Ba ≤ max 0 (max Ba Bb) := (le_max_left Ba Bb).trans (le_max_right _ _)
    dsimp [B]; linarith
  have hbb (x : Base) : |b x| ≤ B := by
    have h := hBb x (mem_univ x)
    rw [Real.norm_eq_abs] at h
    have hh : Bb ≤ max 0 (max Ba Bb) := (le_max_right Ba Bb).trans (le_max_right _ _)
    dsimp [B]; linarith
  let C := finiteChartDerivativeSize P sphereAtlasCore J
    (intrinsicChartCoefficient (roundTensorPerturbation a) b)
  have hC : 0 ≤ C := finiteChartDerivativeSize_nonneg P sphereAtlasCore_compact J _
    (fun p _ ↦ intrinsic_round_increment_smooth a b ha hb p)
  refine ⟨min (c/B) (eps/(C+1)),lt_min (div_pos hc hB) (div_pos heps (by linarith)),?_⟩
  intro t ht
  have htB : |t| * B < c := (lt_div_iff₀ hB).mp (ht.trans_le (min_le_left _ _))
  have htC : |t| * (C+1) < eps := (lt_div_iff₀ (by linarith : 0 < C+1)).mp
    (ht.trans_le (min_le_right _ _))
  obtain ⟨hpos,hden⟩ := round_perturbed_pair_positive A rho (fun x ↦ t*a x) (fun x ↦ t*b x)
    hc hAm hrm
    (fun x ↦ by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hab x) (abs_nonneg t)).trans_lt htB)
    (fun x ↦ by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hbb x) (abs_nonneg t)).trans_lt htB)
  refine ⟨hA.add_section (roundTensorPerturbation_smooth _ (contMDiff_const.mul ha)),?_,hpos,
    hr.add (contMDiff_const.mul hb),hden,?_⟩
  · intro x v w
    change A x v w+(t*a x)*roundCotangentTensor x v w = A x w v+(t*a x)*roundCotangentTensor x w v
    rw [hs,roundCotangentTensor_symm]
  · rw [sphereCoefficientDistance_round_smul P J A rho a b ha hb t]
    change |t| * C < eps
    nlinarith [abs_nonneg t]

end
end Yau.Target

end OAI
