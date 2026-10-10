import OAI.NumberTheory.TwoPointCorrelations.MRTRamareWeights
import OAI.NumberTheory.TwoPointCorrelations.MRTBoundaryMean

namespace OAI

/-! Coarse cofactor windows for a multiplicative prime bin.  The weights
are the actual Ramaré weights, and moving all primes in a bin to its
lower endpoint changes coefficients only in two short boundary strips. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtCoarseRamareWeight (P : Finset ℕ) (L : ℕ → ℝ)
    (N n : ℕ) : ℝ :=
  ∑ p ∈ P, mrtRamareWeight P n p *
    if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then 1 else 0

lemma mrtCoarseRamareWeight_nonneg (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ) :
    0 ≤ mrtCoarseRamareWeight P L N n := by
  apply sum_nonneg
  intro p _
  exact mul_nonneg (mrtRamareWeight_nonneg P n p) (by split_ifs <;> norm_num)

lemma mrt_coarse_weight_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (L : ℕ → ℝ) (N n : ℕ) : mrtCoarseRamareWeight P L N n ≤ 1 := by
  apply le_trans _ (mrt_ramare_weight_sum_le_one P hP n)
  apply sum_le_sum
  intro p _
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]
    exact mrtRamareWeight_nonneg P n p

lemma mrt_coarse_window_support {X δ a p m n : ℝ} (hδ : 1 ≤ δ)
    (hm : 0 ≤ m) (hl : a ≤ p) (hu : p ≤ δ * a) (hn : p * m = n)
    (hwindow : X < a * m ∧ a * m ≤ 2 * X) :
    X < n ∧ n ≤ 2 * δ * X := by
  have h1 := mul_le_mul_of_nonneg_right hl hm
  have h2 := mul_le_mul_of_nonneg_right hu hm
  have h3 := mul_le_mul_of_nonneg_left hwindow.2 (show 0 ≤ δ by linarith)
  constructor <;> nlinarith

lemma mrt_coarse_window_interior {X δ a p m n : ℝ} (hδ : 1 ≤ δ)
    (hm : 0 ≤ m) (hl : a ≤ p) (hu : p ≤ δ * a) (hn : p * m = n)
    (hinterior : δ * X < n ∧ n ≤ 2 * X) :
    X < a * m ∧ a * m ≤ 2 * X := by
  have h1 := mul_le_mul_of_nonneg_right hl hm
  have h2 := mul_le_mul_of_nonneg_right hu hm
  have hd : 0 < δ := by linarith
  constructor
  · apply (mul_lt_mul_iff_right₀ hd).mp
    nlinarith
  · linarith

lemma mrt_coarse_weight_zero (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hn : ¬((N : ℝ) < n ∧ (n : ℝ) ≤ 2 * δ * N)) :
    mrtCoarseRamareWeight P L N n = 0 := by
  apply sum_eq_zero
  intro p hp
  by_cases hpn : p ∣ n
  · have hmul : (p : ℝ) * (n / p : ℕ) = n := by
      exact_mod_cast Nat.mul_div_cancel' hpn
    have hw : ¬((N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N) := by
      intro h
      exact hn (mrt_coarse_window_support hδ (Nat.cast_nonneg _) (hL p hp).1
        (hL p hp).2 hmul h)
    rw [ite_eq_right hw, mul_zero]
  · simp only [mrtRamareWeight, ite_eq_right hpn, zero_mul]

lemma mrt_coarse_weight_interior (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hn : δ * N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N) :
    mrtCoarseRamareWeight P L N n = ∑ p ∈ P, mrtRamareWeight P n p := by
  apply sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · have hmul : (p : ℝ) * (n / p : ℕ) = n := by
      exact_mod_cast Nat.mul_div_cancel' hpn
    have hw := mrt_coarse_window_interior hδ (Nat.cast_nonneg _) (hL p hp).1
      (hL p hp).2 hmul hn
    rw [ite_eq_left hw, mul_one]
  · simp only [mrtRamareWeight, ite_eq_right hpn, zero_mul]

noncomputable def mrtCoarseBoundaryCoefficient (P : Finset ℕ) (L : ℕ → ℝ)
    (N n : ℕ) : ℝ :=
  (if N < n ∧ n ≤ 2 * N then ∑ p ∈ P, mrtRamareWeight P n p else 0) -
    mrtCoarseRamareWeight P L N n

lemma mrt_coarse_boundary_abs (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (L : ℕ → ℝ) (N n : ℕ) : |mrtCoarseBoundaryCoefficient P L N n| ≤ 1 := by
  have hc0 := mrtCoarseRamareWeight_nonneg P L N n
  have hc1 := mrt_coarse_weight_le_one P hP L N n
  have hr0 : 0 ≤ ∑ p ∈ P, mrtRamareWeight P n p :=
    sum_nonneg fun p _ => mrtRamareWeight_nonneg P n p
  have hr1 := mrt_ramare_weight_sum_le_one P hP n
  unfold mrtCoarseBoundaryCoefficient
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

theorem mrt_coarse_boundary_support (P : Finset ℕ) (L : ℕ → ℝ) (N n : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hn : n ∉ mrtBoundarySet N δ) : mrtCoarseBoundaryCoefficient P L N n = 0 := by
  have hnot := mt (mrt_mem_boundary_iff N n hδ).mpr hn
  unfold mrtCoarseBoundaryCoefficient
  by_cases hwindow : N < n ∧ n ≤ 2 * N
  · have hi : δ * N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
      constructor
      · by_contra h
        exact hnot (Or.inl ⟨hwindow.1, le_of_not_gt h⟩)
      · exact_mod_cast hwindow.2
    rw [ite_eq_left hwindow, mrt_coarse_weight_interior P L N n hδ hL hi, sub_self]
  · have ho : ¬((N : ℝ) < n ∧ (n : ℝ) ≤ 2 * δ * N) := by
      rintro ⟨hnN, hnU⟩
      have hnN' : N < n := by exact_mod_cast hnN
      have hn2 : 2 * N < n := by omega
      apply hnot
      right
      refine ⟨hn2, ?_⟩
      convert hnU using 1
      push_cast
      ring
    rw [ite_eq_right hwindow, mrt_coarse_weight_zero P L N n hδ hL ho, sub_self]

end TwoPointCorrelations

end OAI
