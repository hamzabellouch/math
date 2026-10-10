import OAI.Geometry.NodalSets.Waves.EuclideanGaussianSmallBall
import OAI.Geometry.NodalSets.Waves.GaussianJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability
open scoped ContDiff
noncomputable section

lemma real_partial_contDiff (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ fderiv ℝ f x (Pi.single i 1)) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).contDiff.comp
    hdf

lemma real_partial_fderiv_bound (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : Coord) (i : Fin 4) :
    ‖fderiv ℝ (fun z ↦ fderiv ℝ f z (Pi.single i 1)) x‖ ≤
      ‖iteratedFDeriv ℝ 2 f x‖ := by
  let L : (Coord →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa [L,Pi.norm_single] using v.le_opNorm (Pi.single i (1:ℝ))
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd := (L.hasFDerivAt.comp x
    (hdf.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
  change fderiv ℝ (fun z ↦ fderiv ℝ f z (Pi.single i 1)) x = _ at hd
  rw [hd]
  calc
    _ ≤ ‖L‖*‖fderiv ℝ (fderiv ℝ f) x‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*‖fderiv ℝ (fderiv ℝ f) x‖ :=
      mul_le_mul_of_nonneg_right hL (norm_nonneg (fderiv ℝ (fderiv ℝ f) x))
    _ = ‖iteratedFDeriv ℝ 2 f x‖ := by
      rw [one_mul,← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]

lemma scalar_normalization_derivative (q S : Coord → ℝ) {x : Coord} {N : ℝ}
    (hq : DifferentiableAt ℝ q x) (hS : DifferentiableAt ℝ S x)
    (hN : 0 ≤ N) :
    ‖fderiv ℝ (fun z ↦ Real.exp (-N*S z)*q z) x‖ ≤
      Real.exp (-N*S x)*(N*‖fderiv ℝ S x‖*|q x|+‖fderiv ℝ q x‖) := by
  have he := ((hS.hasFDerivAt.const_mul (-N)).exp).mul hq.hasFDerivAt
  change HasFDerivAt (fun z ↦ Real.exp (-N*S z)*q z) _ x at he
  rw [he.fderiv]
  have h := norm_add_le
    (Real.exp (-N*S x) • fderiv ℝ q x)
    (q x • (Real.exp (-N*S x) • (-N • fderiv ℝ S x)))
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),abs_neg,
    abs_of_nonneg hN] at h
  convert h using 1
  ring

lemma jet_vector_fderiv_bound (q : Fin 5 → Coord → ℝ) (x : Coord)
    (hq : ∀ i, DifferentiableAt ℝ (q i) x) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, ‖fderiv ℝ (q i) x‖ ≤ B) :
    ‖fderiv ℝ (fun z ↦ WithLp.toLp 2 (fun i ↦ q i z)) x‖ ≤ 6*B := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 ↦ ℝ)).symm.toContinuousLinearMap
  have hq' : HasFDerivAt (fun z i ↦ q i z)
      (ContinuousLinearMap.pi (fun i ↦ fderiv ℝ (q i) x)) x :=
    hasFDerivAt_pi.mpr (fun i ↦ (hq i).hasFDerivAt)
  have hd := (L.hasFDerivAt.comp x hq').fderiv
  change fderiv ℝ (fun z ↦ WithLp.toLp 2 (fun i ↦ q i z)) x = _ at hd
  rw [hd]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖WithLp.toLp 2 (fun i ↦ fderiv ℝ (q i) x v)‖ ≤ _
  have h := euclidean_toLp_norm_le (fun i ↦ fderiv ℝ (q i) x v)
  have hp : ‖fun i ↦ fderiv ℝ (q i) x v‖ ≤ B*‖v‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact ((fderiv ℝ (q i) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg v))
  norm_num at h
  nlinarith

lemma normalizedRealJet_fderiv_le (f S : Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (hS : ContDiff ℝ ∞ S) (x : Coord) {N : ℝ} (hN : 0 ≤ N) :
    ‖fderiv ℝ (fun z ↦ normalizedRealJet f N (S z) z) x‖ ≤
      6*Real.exp (-N*S x)*(N*‖fderiv ℝ S x‖*
        max |f x| (N⁻¹*‖fderiv ℝ f x‖)+
        max ‖fderiv ℝ f x‖ (N⁻¹*‖iteratedFDeriv ℝ 2 f x‖)) := by
  let q : Fin 5 → Coord → ℝ := fun i z ↦
    (Fin.cons (f z) (fun j : Fin 4 ↦ N⁻¹*fderiv ℝ f z (Pi.single j 1)) : Fin 5 → ℝ) i
  have hq (i : Fin 5) : ContDiff ℝ ∞ (q i) := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hf
    · exact contDiff_const.mul (real_partial_contDiff f hf j)
  have hv (i : Fin 5) : |q i x| ≤ max |f x| (N⁻¹*‖fderiv ℝ f x‖) := by
    refine Fin.cases (le_max_left _ _) (fun j ↦ ?_) i
    change |N⁻¹*fderiv ℝ f x (Pi.single j 1)| ≤ _
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hN)]
    apply le_trans ?_ (le_max_right _ _)
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hN)
    simpa [Pi.norm_single] using (fderiv ℝ f x).le_opNorm (Pi.single j (1:ℝ))
  have hd (i : Fin 5) : ‖fderiv ℝ (q i) x‖ ≤
      max ‖fderiv ℝ f x‖ (N⁻¹*‖iteratedFDeriv ℝ 2 f x‖) := by
    refine Fin.cases (le_max_left _ _) (fun j ↦ ?_) i
    change ‖fderiv ℝ (fun z ↦ N⁻¹*fderiv ℝ f z (Pi.single j 1)) x‖ ≤ _
    rw [((real_partial_contDiff f hf j).differentiable (by simp)).differentiableAt.hasFDerivAt.const_mul N⁻¹ |>.fderiv]
    change ‖N⁻¹ • fderiv ℝ (fun z ↦ fderiv ℝ f z (Pi.single j 1)) x‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hN)]
    exact (mul_le_mul_of_nonneg_left (real_partial_fderiv_bound f hf x j)
      (inv_nonneg.mpr hN)).trans (le_max_right _ _)
  have heq : (fun z ↦ normalizedRealJet f N (S z) z) =
      fun z ↦ WithLp.toLp 2 (fun i ↦ Real.exp (-N*S z)*q i z) := by
    funext z
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [normalizedRealJet,q,mul_assoc]
  rw [heq]
  have hds := (hS.differentiable (by simp)).differentiableAt (x := x)
  have h := jet_vector_fderiv_bound (fun i z ↦ Real.exp (-N*S z)*q i z) x
    (fun i ↦ ((hds.const_mul (-N)).exp).mul ((hq i).differentiable (by simp)).differentiableAt)
    (B := Real.exp (-N*S x)*(N*‖fderiv ℝ S x‖*max |f x| (N⁻¹*‖fderiv ℝ f x‖)+
      max ‖fderiv ℝ f x‖ (N⁻¹*‖iteratedFDeriv ℝ 2 f x‖))) (by positivity) (fun i ↦ ?_)
  · simpa [mul_assoc] using h
  · exact (scalar_normalization_derivative (q i) S
      ((hq i).differentiable (by simp)).differentiableAt hds hN).trans (by gcongr; exact hv i; exact hd i)

end
end Yau.Geometry

end OAI
