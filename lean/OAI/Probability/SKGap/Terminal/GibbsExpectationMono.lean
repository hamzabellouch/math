import Mathlib
import OAI.Probability.SKGap.Localization.Centered

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff

lemma gibbsExpectation_mono {n : ℕ} (J : Interaction n) (f g : Observables n)
    (hfg : ∀ x, f x ≤ g x) : gibbsExpectation J f ≤ gibbsExpectation J g := by
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (le_of_lt (gibbs_pos J x))

lemma spin_variance {n : ℕ} (J : Interaction n) (i : Fin n) :
    gibbsVariance J (fun x => spin x i) = 1 := by
  rw [gibbsVariance, gibbs_spin_centered]
  simp only [sub_zero, spin_sq]
  exact gibbsExpectation_const J 1

theorem finite_gap_le_one {n : ℕ} (hn : 0 < n) (J : Interaction n)
    {γ : ℝ} (hγ : HasGap J γ) : γ ≤ 1 := by
  let i : Fin n := ⟨0, hn⟩
  have hh := hγ (fun x => spin x i)
  rw [spin_variance, mul_one] at hh
  have hd : dirichlet J (fun x => spin x i) (fun x => spin x i) =
      gibbsExpectation J (fun x => siteVariance J x i) := by
    simp [dirichlet, halfDiff_spin]
  rw [hd] at hh
  exact hh.trans ((gibbsExpectation_mono J _ (fun _ => 1)
    (fun x => siteVariance_le_one J x i)).trans_eq (gibbsExpectation_const J 1))

lemma spectral_bilinear_dirichlet {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (f g : Observables n) :
    dirichlet J f g = ∑ a, spinEigenvalues J hJ hdiag a *
      ((spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J f) a) *
      ((spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J g) a) := by
  rw [← gibbs_dirichlet J hJ hdiag]
  change stationaryInner J f (-generator J g) = _
  rw [← spectral_parseval J hJ hdiag]
  simp_rw [spectral_generator_coordinates]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma spectral_gradient_correlation {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (t : ℝ) (f g : Observables n) :
    weightedInner J (gradientCLM n f) (gradientSemigroup J t (gradientCLM n g)) =
      ∑ a, spinEigenvalues J hJ hdiag a * Real.exp (-spinEigenvalues J hJ hdiag a * t) *
      ((spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J f) a) *
      ((spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J g) a) := by
  change weightedInner J (fun x i => halfDiff i f x)
    (gradientSemigroup J t (fun x i => halfDiff i g x)) = _
  simp_rw [weightedInner, ← halfDiff_semigroup]
  change dirichlet J f (semigroup J t g) = _
  rw [spectral_bilinear_dirichlet J hJ hdiag]
  simp_rw [spectral_semigroup_coordinates]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem exact_gradient_semigroup_positive {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (t : ℝ) (f : Observables n) :
    0 ≤ weightedInner J (gradientCLM n f) (gradientSemigroup J t (gradientCLM n f)) := by
  rw [spectral_gradient_correlation J hJ hdiag]
  apply Finset.sum_nonneg
  intro a _
  rw [mul_assoc]
  exact mul_nonneg (mul_nonneg (spinEigenvalues_nonneg J hJ hdiag a)
    (le_of_lt (Real.exp_pos _))) (mul_self_nonneg _)

lemma exact_gradient_semigroup_symmetric {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (t : ℝ) (f g : Observables n) :
    weightedInner J (gradientCLM n f) (gradientSemigroup J t (gradientCLM n g)) =
      weightedInner J (gradientCLM n g) (gradientSemigroup J t (gradientCLM n f)) := by
  rw [spectral_gradient_correlation J hJ hdiag, spectral_gradient_correlation J hJ hdiag]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem exact_gradient_semigroup_gap {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    {γ : ℝ} (hγ : HasGap J γ) (t : ℝ) (ht : 0 ≤ t) (f : Observables n) :
    weightedInner J (gradientSemigroup J t (gradientCLM n f))
      (gradientSemigroup J t (gradientCLM n f)) ≤
      Real.exp (-2 * γ * t) * weightedInner J (gradientCLM n f) (gradientCLM n f) := by
  have hg : gradientSemigroup J t (gradientCLM n f) = gradientCLM n (semigroup J t f) := by
    ext x i
    exact (halfDiff_semigroup J t f x i).symm
  rw [hg]
  change dirichlet J (semigroup J t f) (semigroup J t f) ≤ Real.exp (-2 * γ * t) * dirichlet J f f
  rw [spectral_dirichlet J hJ hdiag, spectral_dirichlet J hJ hdiag, Finset.mul_sum]
  simp_rw [spectral_semigroup_coordinates]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : spinEigenvalues J hJ hdiag a = 0
  · simp only [ha, zero_mul, mul_zero, le_refl]
  · have hp := lt_of_le_of_ne (spinEigenvalues_nonneg J hJ hdiag a) (Ne.symm ha)
    have hle := gap_le_positive_eigenvalue J hJ hdiag hγ a hp
    have he : Real.exp (-spinEigenvalues J hJ hdiag a * t) ^ 2 ≤ Real.exp (-2 * γ * t) := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      norm_num only [Nat.cast_ofNat]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hle) ht]
    have hm := mul_le_mul_of_nonneg_right he
      (mul_nonneg (le_of_lt hp)
        (sq_nonneg ((spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J f) a)))
    convert hm using 1
    ring

end SKGapCutoff

open scoped BigOperators

end

end OAI
