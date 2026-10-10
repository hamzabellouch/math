import Mathlib
import OAI.Probability.SKGap.Localization.Magnetization
import OAI.Probability.SKGap.Terminal.GibbsExpectationMono
import OAI.Probability.SKGap.Localization.CubeWeight

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace SKGapCutoff

lemma stationary_deviation_le_oscillation {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (C : ℝ) (hf : ∀ y, f x - f y ≤ C) :
    f x - gibbsExpectation J f ≤ C := by
  have h := gibbsExpectation_mono J (fun y => f x - f y) (fun _ => C) hf
  simpa only [gibbsExpectation_sub, gibbsExpectation_const] using h

lemma semigroup_deviation_le_gradient {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (t : ℝ) (f : Observables n) (C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ y, ∑ i, (halfDiff i (semigroup J t f) y) ^ 2 ≤ C ^ 2) (x : Spin n) :
    semigroup J t f x - gibbsExpectation J f ≤ 2 * Real.sqrt n * C := by
  rw [← gibbsExpectation_semigroup J hJ hdiag t f]
  apply stationary_deviation_le_oscillation J _ x
  intro y
  exact (le_abs_self _).trans (euclidean_oscillation _ C hC hgrad x y)

theorem continuous_tv_le_gradient {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (t C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ f : Observables n, (∀ y, |f y| ≤ 1) →
      ∀ y, ∑ i, (halfDiff i (semigroup J t f) y) ^ 2 ≤ C ^ 2) (x : Spin n) :
    totalVariation (continuousKernel J t x) (gibbs J) ≤ Real.sqrt n * C := by
  let f : Observables n := fun y => if 0 ≤ continuousKernel J t x y - gibbs J y then 1 else -1
  have hf (y : Spin n) : |f y| ≤ 1 := by dsimp [f]; split_ifs <;> norm_num
  have he : semigroup J t f x - gibbsExpectation J f =
      2 * totalVariation (continuousKernel J t x) (gibbs J) := by
    rw [← kernel_apply (semigroup J t) f x]
    simp only [gibbsExpectation, totalVariation, mul_div_cancel₀ _ (show (2 : ℝ) ≠ 0 by norm_num),
      ← Finset.sum_sub_distrib, ← sub_mul]
    apply Finset.sum_congr rfl
    intro y _
    change (continuousKernel J t x y - gibbs J y) * f y = |continuousKernel J t x y - gibbs J y|
    dsimp [f]
    split_ifs with h
    · rw [mul_one, abs_of_nonneg h]
    · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]
  have hb := semigroup_deviation_le_gradient J hJ hdiag t f C hC (hgrad f hf) x
  rw [he] at hb
  nlinarith

lemma worstContinuous_le_gradient {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (t C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ f : Observables n, (∀ y, |f y| ≤ 1) →
      ∀ y, ∑ i, (halfDiff i (semigroup J t f) y) ^ 2 ≤ C ^ 2) :
    worstContinuous J t ≤ Real.sqrt n * C := by
  exact Finset.sup'_le _ _ (fun x _ => continuous_tv_le_gradient J hJ hdiag t C hC hgrad x)

noncomputable def linearObservable {n : ℕ} (u : Fin n → ℝ) (x : Spin n) : ℝ :=
  ∑ i, u i * spin x i

lemma halfDiff_linearObservable {n : ℕ} (u : Fin n → ℝ) (x : Spin n) (i : Fin n) :
    halfDiff i (linearObservable u) x = u i := by
  have hmul (c : ℝ) (f : Observables n) :
      halfDiff i (fun y => c * f y) x = c * halfDiff i f x := by
    simp only [halfDiff]
    ring
  change halfDiff i (fun y => ∑ j, u j * spin y j) x = _
  simp only [halfDiff_sum, hmul, halfDiff_spin]
  simp

lemma linearObservable_centered {n : ℕ} (J : Interaction n) (u : Fin n → ℝ) :
    gibbsExpectation J (linearObservable u) = 0 := by
  change gibbsExpectation J (fun x => ∑ i, u i * spin x i) = 0
  simp only [gibbsExpectation_sum, gibbsExpectation_mul_const,
    gibbs_spin_centered, mul_zero, Finset.sum_const_zero]

lemma dirichlet_linearObservable_le {n : ℕ} (J : Interaction n) (u : Fin n → ℝ) :
    dirichlet J (linearObservable u) (linearObservable u) ≤ ∑ i, u i ^ 2 := by
  simp only [dirichlet, halfDiff_linearObservable]
  calc
    _ ≤ gibbsExpectation J (fun _ => ∑ i, u i ^ 2) := by
      apply gibbsExpectation_mono
      intro x
      apply Finset.sum_le_sum
      intro i _
      rw [mul_assoc, ← pow_two]
      exact mul_le_of_le_one_left (sq_nonneg _) (siteVariance_le_one J x i)
    _ = _ := gibbsExpectation_const J _

lemma linearObservable_second_moment_le {n : ℕ} (J : Interaction n)
    {γ V : ℝ} (hγ : 0 < γ) (hgap : HasGap J γ) (hV : 1 ≤ γ * V)
    (u : Fin n → ℝ) :
    gibbsExpectation J (fun x => linearObservable u x ^ 2) ≤ V * ∑ i, u i ^ 2 := by
  have hg := (hgap (linearObservable u)).trans (dirichlet_linearObservable_le J u)
  rw [gibbsVariance, linearObservable_centered] at hg
  simp only [sub_zero] at hg
  apply (mul_le_mul_iff_right₀ hγ).mp
  calc
    γ * gibbsExpectation J (fun x => linearObservable u x ^ 2) ≤ ∑ i, u i ^ 2 := hg
    _ ≤ γ * (V * ∑ i, u i ^ 2) := by
      have h := mul_le_mul_of_nonneg_right hV
        (show (0 : ℝ) ≤ ∑ i, u i ^ 2 from Finset.sum_nonneg (fun i _ => sq_nonneg (u i)))
      simpa only [one_mul, mul_assoc] using h

noncomputable def overlap {n : ℕ} (x y : Spin n) : ℝ := linearObservable (spin x) y

lemma overlap_coeff_norm_sq {n : ℕ} (x : Spin n) : ∑ i, spin x i ^ 2 = (n : ℝ) := by simp

noncomputable def spinCorrelation {n : ℕ} (J : Interaction n) (t : ℝ) : ℝ :=
  (∑ i, stationaryInner J (fun x => spin x i) (semigroup J t (fun x => spin x i))) / n

lemma overlap_correlates {n : ℕ} (hn : 0 < n) (J : Interaction n) (t : ℝ) :
    gibbsExpectation J (fun x => semigroup J t (overlap x) x) =
      (n : ℝ) * spinCorrelation J t := by
  have hs (x : Spin n) : semigroup J t (overlap x) x =
      ∑ i, spin x i * semigroup J t (fun y => spin y i) x := by
    have heq : overlap x = ∑ i, spin x i • (fun y => spin y i) := by
      funext y
      simp only [overlap, linearObservable, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hs, gibbsExpectation_sum, stationaryInner, spinCorrelation]
  field_simp

lemma exists_overlap_mean_ge {n : ℕ} (hn : 0 < n) (J : Interaction n) (t : ℝ) :
    ∃ x, (n : ℝ) * spinCorrelation J t ≤ semigroup J t (overlap x) x := by
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image (Finset.univ : Finset (Spin n))
    (fun x => semigroup J t (overlap x) x) Finset.univ_nonempty
  refine ⟨x, ?_⟩
  rw [← overlap_correlates hn J t]
  exact (gibbsExpectation_mono J _ (fun _ => semigroup J t (overlap x) x)
    (fun y => hx y (Finset.mem_univ y))).trans_eq (gibbsExpectation_const J _)

lemma kernel_centered_second_moment {n : ℕ} (J : Interaction n) (t : ℝ)
    (f : Observables n) (x : Spin n) :
    ∑ y, continuousKernel J t x y * (f y - semigroup J t f x) ^ 2 =
      semigroup J t (fun y => f y ^ 2) x - (semigroup J t f x) ^ 2 := by
  simpa only [zero_add] using
    quadratic_centered_identity (continuousKernel J t x) f (semigroup J t f x) 0
      (semigroup J t (fun y => f y ^ 2) x) (continuousKernel_sum J t x)
      (kernel_apply _ _ _)
      (by simpa only [sub_zero, continuousKernel] using kernel_apply (semigroup J t) (fun y => f y ^ 2) x)

theorem worstContinuous_lower_from_spin {n : ℕ} (hn : 0 < n) (J : Interaction n)
    {γ V c t : ℝ} (ht : 0 ≤ t) (hγ : 0 < γ) (hgap : HasGap J γ)
    (hV : 1 ≤ γ * V) (hc : 0 < c) (hcor : c ≤ spinCorrelation J t)
    (hvar : ∀ x, semigroup J t (fun y => overlap x y ^ 2) x -
      (semigroup J t (overlap x) x) ^ 2 ≤ (n : ℝ) * V) :
    (n : ℝ) * c ^ 2 * (1 - worstContinuous J t) ≤ 8 * V := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨x, hx⟩ := exists_overlap_mean_ge hn J t
  let m := semigroup J t (overlap x) x
  have hm : (n : ℝ) * c ≤ m := (mul_le_mul_of_nonneg_left hcor hn'.le).trans hx
  have hmpos : 0 < m := (mul_pos hn' hc).trans_le hm
  have heq : ∑ y, gibbs J y * overlap x y ^ 2 ≤ (n : ℝ) * V := by
    have h := linearObservable_second_moment_le J hγ hgap hV (spin x)
    simpa only [overlap_coeff_norm_sq, mul_comm, gibbsExpectation, overlap] using h
  have htrans : ∑ y, continuousKernel J t x y * (overlap x y - m) ^ 2 ≤ (n : ℝ) * V := by
    rw [kernel_centered_second_moment]
    exact hvar x
  have htv := totalVariation_lower_from_quadratic_test (continuousKernel J t x) (gibbs J)
    (overlap x) (continuousKernel_nonneg J t ht x) (fun y => (gibbs_pos J y).le)
    (continuousKernel_sum J t x) (gibbs_sum J) m ((n : ℝ) * V) hmpos htrans heq
  have hmax : totalVariation (continuousKernel J t x) (gibbs J) ≤ worstContinuous J t :=
    Finset.le_sup' (f := fun y => totalVariation (continuousKernel J t y) (gibbs J))
      (Finset.mem_univ x)
  have hnonneg : 0 ≤ 1 - worstContinuous J t := sub_nonneg.mpr (worstContinuous_le_one J t ht)
  have hsquare : ((n : ℝ) * c) ^ 2 ≤ m ^ 2 := sq_le_sq₀ (mul_pos hn' hc).le hmpos.le |>.mpr hm
  have h := calc
    (n : ℝ) * ((n : ℝ) * c ^ 2 * (1 - worstContinuous J t)) =
        ((n : ℝ) * c) ^ 2 * (1 - worstContinuous J t) := by ring
    _ ≤ m ^ 2 * (1 - worstContinuous J t) := mul_le_mul_of_nonneg_right hsquare hnonneg
    _ ≤ m ^ 2 * (1 - totalVariation (continuousKernel J t x) (gibbs J)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hmax 1) (sq_nonneg m)
    _ ≤ (n : ℝ) * (8 * V) := by nlinarith [htv]
  exact (mul_le_mul_iff_right₀ hn').mp h

end SKGapCutoff

end

end OAI
