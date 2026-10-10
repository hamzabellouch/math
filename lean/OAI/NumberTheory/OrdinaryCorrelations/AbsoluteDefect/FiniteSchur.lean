import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinarySparseSieve

lemma finite_schur {ι : Type*} (s : Finset ι) (a : ι → ℝ) (K : ι → ι → ℝ)
    (R : ℝ) (hK : ∀ m ∈ s, ∀ n ∈ s, 0 ≤ K m n)
    (hsym : ∀ m ∈ s, ∀ n ∈ s, K m n = K n m)
    (hrow : ∀ m ∈ s, ∑ n ∈ s, K m n ≤ R) :
    ∑ m ∈ s, ∑ n ∈ s, a m * a n * K m n ≤ R * ∑ m ∈ s, (a m)^2 := by
  have heq : (∑ m ∈ s, ∑ n ∈ s, ((a m)^2 + (a n)^2) * K m n) =
      2 * ∑ m ∈ s, (a m)^2 * ∑ n ∈ s, K m n := by
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun m n => (a n)^2 * K m n)]
    have hsym' : (∑ n ∈ s, ∑ m ∈ s, (a n)^2 * K m n) =
        ∑ n ∈ s, ∑ m ∈ s, (a n)^2 * K n m := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      rw [hsym m hm n hn]
    rw [hsym']
    simp_rw [← Finset.mul_sum]
    ring
  have h := Finset.sum_le_sum (s := s) (fun m hm =>
    Finset.sum_le_sum (s := s) (fun n hn =>
      mul_le_mul_of_nonneg_right (show 2 * (a m * a n) ≤ (a m)^2 + (a n)^2 by
        nlinarith [sq_nonneg (a m - a n)]) (hK m hm n hn)))
  simp_rw [mul_assoc, ← Finset.mul_sum] at h
  rw [heq] at h
  have hb : (∑ m ∈ s, (a m)^2 * ∑ n ∈ s, K m n) ≤ R * ∑ m ∈ s, (a m)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg (a m))
  simp_rw [mul_assoc, ← Finset.mul_sum]
  linarith

noncomputable def weightedGram {ι κ : Type*} (A : Finset ι) (w : ι → ℝ)
    (v : κ → ι → ℂ) (j k : κ) : ℂ := ∑ n ∈ A, (w n : ℂ)*v j n*star (v k n)

lemma weightedGram_symm {ι κ : Type*} (A : Finset ι) (w : ι → ℝ)
    (v : κ → ι → ℂ) (j k : κ) :
    ‖weightedGram A w v j k‖ = ‖weightedGram A w v k j‖ := by
  have he : star (weightedGram A w v j k) = weightedGram A w v k j := by
    simp only [weightedGram, star_sum, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    apply sum_congr rfl
    intro n hn
    ring
  rw [← he, norm_star]

lemma weighted_dual_energy {ι κ : Type*} (A : Finset ι) (T : Finset κ)
    (w : ι → ℝ) (v : κ → ι → ℂ) (c : κ → ℂ)
    (hw : ∀ n ∈ A, 0 ≤ w n) {R : ℝ}
    (hrow : ∀ j ∈ T, ∑ k ∈ T, ‖weightedGram A w v j k‖ ≤ R) :
    (∑ n ∈ A, w n * ‖∑ j ∈ T, c j*v j n‖^2) ≤ R * ∑ j ∈ T, ‖c j‖^2 := by
  have he : ((∑ n ∈ A, w n * ‖∑ j ∈ T, c j*v j n‖^2 : ℝ) : ℂ) =
      ∑ j ∈ T, ∑ k ∈ T, c j*star (c k)*weightedGram A w v j k := by
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum]
    simp_rw [sum_mul_sum, mul_sum, weightedGram, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    rw [sum_comm]
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro n hn
    simp only [map_mul, Complex.star_def]
    ring
  calc
    _ = ‖((∑ n ∈ A, w n * ‖∑ j ∈ T, c j*v j n‖^2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact sum_nonneg (fun n hn => mul_nonneg (hw n hn) (sq_nonneg _))
    _ = ‖∑ j ∈ T, ∑ k ∈ T, c j*star (c k)*weightedGram A w v j k‖ := congrArg norm he
    _ ≤ ∑ j ∈ T, ∑ k ∈ T, ‖c j‖*‖c k‖*‖weightedGram A w v j k‖ := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro j hj
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, norm_star])
    _ ≤ _ := finite_schur T (fun j => ‖c j‖) (fun j k => ‖weightedGram A w v j k‖) R
      (fun _ _ _ _ => norm_nonneg _) (fun j _ k _ => weightedGram_symm A w v j k) hrow

lemma complex_cauchy_sq {ι : Type*} (S : Finset ι) (a b : ι → ℂ) :
    ‖∑ n ∈ S, a n*b n‖^2 ≤ (∑ n ∈ S, ‖a n‖^2)*(∑ n ∈ S, ‖b n‖^2) := by
  calc
    _ ≤ (∑ n ∈ S, ‖a n‖*‖b n‖)^2 := by
      gcongr
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ _ := sum_mul_sq_le_sq_mul_sq S (fun n => ‖a n‖) (fun n => ‖b n‖)

theorem sparse_majorant_duality {ι κ : Type*} (S A : Finset ι) (T : Finset κ)
    (a : ι → ℂ) (w : ι → ℝ) (v : κ → ι → ℂ)
    (hSA : S ⊆ A) (hw : ∀ n ∈ A, 0 ≤ w n) (hmajor : ∀ n ∈ S, 1 ≤ w n)
    {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ j ∈ T, ∑ k ∈ T, ‖weightedGram A w v j k‖ ≤ R) :
    (∑ j ∈ T, ‖∑ n ∈ S, a n*v j n‖^2) ≤ R*(∑ n ∈ S, ‖a n‖^2) := by
  let P : κ → ℂ := fun j => ∑ n ∈ S, a n*v j n
  let B : ι → ℂ := fun n => ∑ j ∈ T, star (P j)*v j n
  let E : ℝ := ∑ j ∈ T, ‖P j‖^2
  let C : ℝ := ∑ n ∈ S, ‖a n‖^2
  have hE : 0 ≤ E := sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => sq_nonneg _)
  have hi : (E : ℂ) = ∑ n ∈ S, a n*B n := by
    simp only [E, B, Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.mul_conj']
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    change P j*star (P j) = _
    rw [show P j = ∑ n ∈ S, a n*v j n from rfl, sum_mul]
    apply sum_congr rfl
    intro n hn
    ring
  have hb : (∑ n ∈ S, ‖B n‖^2) ≤ R*E := by
    calc
      _ ≤ ∑ n ∈ S, w n*‖B n‖^2 := sum_le_sum (fun n hn => by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmajor n hn) (sq_nonneg ‖B n‖))
      _ ≤ ∑ n ∈ A, w n*‖B n‖^2 := sum_le_sum_of_subset_of_nonneg hSA (fun n hn _ =>
        mul_nonneg (hw n hn) (sq_nonneg _))
      _ ≤ _ := by
        have hh := weighted_dual_energy A T w v (fun j => star (P j)) hw hrow
        simpa only [B, E, norm_star] using hh
  have hc := complex_cauchy_sq S a B
  rw [← hi, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE] at hc
  have he : E^2 ≤ C*(R*E) := hc.trans (mul_le_mul_of_nonneg_left hb hC)
  change E ≤ R*C
  by_cases hz : E = 0
  · rw [hz]; positivity
  · have hp : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
    nlinarith

end OrdinarySparseSieve

end

end OAI
