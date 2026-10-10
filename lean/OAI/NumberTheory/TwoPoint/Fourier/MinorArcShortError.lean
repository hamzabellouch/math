import OAI.NumberTheory.TwoPoint.Fourier.MinorArcRamareError
import Mathlib.Analysis.PSeries

namespace OAI

/-! Averaging the prime-square correction over literal short windows. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma minor_arc_square_reciprocal_sum (P : Finset ℕ) (R N : ℕ) (hR : 0 < R)
    (hP : ∀ p ∈ P, R ≤ p ∧ p ≤ N) :
    (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 2 / (R : ℝ) := by
  have hsub : P ⊆ Ioo (R - 1) (N + 1) := by
    intro p hp
    have hh := hP p hp
    exact mem_Ioo.mpr ⟨by omega, by omega⟩
  calc
    _ ≤ ∑ p ∈ Ioo (R - 1) (N + 1), ((p : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 / ((R - 1 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le (R - 1) (N + 1)
    _ = _ := by rw [Nat.cast_sub (by omega : 1 ≤ R)]; push_cast; ring

lemma minor_arc_origin_weight_count (X H n : ℕ) :
    ((range X).filter (fun k => k < n ∧ n ≤ k + H)).card ≤ H := by
  have hs : (range X).filter (fun k => k < n ∧ n ≤ k + H) ⊆ Ico (n - H) n := by
    intro k hk
    have h := (mem_filter.mp hk).2
    exact mem_Ico.mpr ⟨by omega, h.1⟩
  apply (card_le_card hs).trans
  rw [Nat.card_Ico]
  omega

lemma minor_arc_window_mass (X H : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    (∑ k ∈ range X, ∑ n ∈ Icc (k + 1) (k + H), w n) ≤
      (H : ℝ) * ∑ n ∈ Icc 1 (X + H), w n := by
  have he (k : ℕ) (hk : k ∈ range X) :
      (∑ n ∈ Icc (k + 1) (k + H), w n) =
        ∑ n ∈ Icc 1 (X + H), if k < n ∧ n ≤ k + H then w n else 0 := by
    have hf : (Icc 1 (X + H)).filter (fun n => k < n ∧ n ≤ k + H) =
        Icc (k + 1) (k + H) := by
      ext n
      have hkX := mem_range.mp hk
      simp only [mem_filter, mem_Icc]
      omega
    rw [← sum_filter, hf]
  calc
    _ = ∑ k ∈ range X, ∑ n ∈ Icc 1 (X + H),
        if k < n ∧ n ≤ k + H then w n else 0 := sum_congr rfl he
    _ = ∑ n ∈ Icc 1 (X + H), ∑ k ∈ range X,
        if k < n ∧ n ≤ k + H then w n else 0 := sum_comm
    _ = ∑ n ∈ Icc 1 (X + H),
        (((range X).filter (fun k => k < n ∧ n ≤ k + H)).card : ℝ) * w n := by
      simp only [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ Icc 1 (X + H), (H : ℝ) * w n := by
      apply sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_right
        ((Nat.cast_le (α := ℝ)).mpr (minor_arc_origin_weight_count X H n)) (hw n)
    _ = _ := (mul_sum _ _ _).symm

lemma minor_arc_prime_square_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N, mrtPrimeSquareCount P n) ≤
      (N : ℝ) * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
  unfold mrtPrimeSquareCount
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro p hp
  rw [mrt_count_multiples (pow_pos (hP p hp).pos 2)]
  convert (Nat.cast_div_le (m := N) (n := p ^ 2) :
    ((N / p ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (p ^ 2 : ℕ)) using 1
  push_cast
  ring

lemma minor_arc_short_square_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (E : ℕ → ℂ) (X H : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hE : ∀ n, 0 < n → n ≤ X + H → ‖E n‖ ≤ A * mrtPrimeSquareCount P n)
    (α : ℝ) :
    (∑ k ∈ range X, ‖shortExponentialSum E H α k‖) ≤
      A * (H : ℝ) * (X + H) * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
  have hpoint (k : ℕ) (hk : k ∈ range X) :
      ‖shortExponentialSum E H α k‖ ≤ A * ∑ n ∈ Icc (k + 1) (k + H),
        mrtPrimeSquareCount P n := by
    rw [shortExponentialSum_at_nat]
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    rw [norm_mul, norm_additiveCharacter, mul_one]
    have hnI := mem_Icc.mp hn
    have hkX := mem_range.mp hk
    exact hE n (by omega) (by omega)
  calc
    _ ≤ ∑ k ∈ range X, A * ∑ n ∈ Icc (k + 1) (k + H), mrtPrimeSquareCount P n :=
      sum_le_sum hpoint
    _ = A * ∑ k ∈ range X, ∑ n ∈ Icc (k + 1) (k + H), mrtPrimeSquareCount P n :=
      (mul_sum _ _ _).symm
    _ ≤ A * ((H : ℝ) * ∑ n ∈ Icc 1 (X + H), mrtPrimeSquareCount P n) :=
      mul_le_mul_of_nonneg_left (minor_arc_window_mass X H _ (mrtPrimeSquareCount_nonneg P)) hA
    _ ≤ A * ((H : ℝ) * ((X + H : ℕ) * ∑ p ∈ P, 1 / (p : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact mul_le_mul_of_nonneg_left (minor_arc_prime_square_mass P hP (X + H)) (Nat.cast_nonneg H)
    _ = _ := by push_cast; ring

end TwoPointCorrelations

end OAI
