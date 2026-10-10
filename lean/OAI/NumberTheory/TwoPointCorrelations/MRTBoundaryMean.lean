import OAI.NumberTheory.TwoPointCorrelations.MRTDyadicMeanSquare

namespace OAI

/-! The two boundary strips created by replacing prime-dependent
cofactor cutoffs with endpoints of a multiplicative prime bin. -/

namespace TwoPointCorrelations

open Finset MeasureTheory

noncomputable def mrtBoundarySet (N : ℕ) (δ : ℝ) : Finset ℕ :=
  Ioc N ⌊δ * (N : ℝ)⌋₊ ∪ Ioc (2 * N) ⌊δ * (2 * N : ℕ)⌋₊

lemma mrt_mem_boundary_iff (N n : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) :
    n ∈ mrtBoundarySet N δ ↔
      (N < n ∧ (n : ℝ) ≤ δ * N) ∨
        (2 * N < n ∧ (n : ℝ) ≤ δ * (2 * N : ℕ)) := by
  have hδ0 : 0 ≤ δ := by linarith
  simp only [mrtBoundarySet, mem_union, mem_Ioc,
    Nat.le_floor_iff (mul_nonneg hδ0 (Nat.cast_nonneg N)),
    Nat.le_floor_iff (mul_nonneg hδ0 (Nat.cast_nonneg (2 * N)))]

lemma mrt_boundary_strip_card (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) :
    ((Ioc N ⌊δ * (N : ℝ)⌋₊).card : ℝ) ≤ (δ - 1) * N := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl : (N : ℝ) ≤ δ * N := by nlinarith
  have hf : N ≤ ⌊δ * (N : ℝ)⌋₊ := Nat.le_floor hl
  rw [Nat.card_Ioc, Nat.cast_sub hf]
  have hu := Nat.floor_le (show 0 ≤ δ * (N : ℝ) by positivity)
  nlinarith

theorem mrt_boundary_card (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) :
    ((mrtBoundarySet N δ).card : ℝ) ≤ 3 * (δ - 1) * N := by
  have hc := card_union_le (Ioc N ⌊δ * (N : ℝ)⌋₊)
    (Ioc (2 * N) ⌊δ * (2 * N : ℕ)⌋₊)
  have hc' : ((mrtBoundarySet N δ).card : ℝ) ≤
      ((Ioc N ⌊δ * (N : ℝ)⌋₊).card : ℝ) +
        ((Ioc (2 * N) ⌊δ * (2 * N : ℕ)⌋₊).card : ℝ) := by
    exact_mod_cast hc
  have h1 := mrt_boundary_strip_card N hδ
  have h2 := mrt_boundary_strip_card (2 * N) hδ
  conv at h2 => rhs; rw [Nat.cast_mul, Nat.cast_ofNat]
  linarith

lemma mrt_boundary_range {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : δ ≤ 2)
    {n : ℕ} (hn : n ∈ mrtBoundarySet N δ) : N < n ∧ n ≤ 4 * N := by
  have hn' := mem_union.mp hn
  have hh : ∀ M : ℕ, ⌊δ * (M : ℝ)⌋₊ ≤ 2 * M := by
    intro M
    apply Nat.floor_le_of_le
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right hδ (show (0 : ℝ) ≤ M from Nat.cast_nonneg M)
  rcases hn' with hn' | hn'
  · have hd := mem_Ioc.mp hn'
    exact ⟨hd.1, (hd.2.trans (hh N)).trans (by omega)⟩
  · have hd := mem_Ioc.mp hn'
    have hu := hd.2.trans (hh (2 * N))
    exact ⟨by omega, by omega⟩

/-- Arbitrary bounded coefficients on the two bin-boundary strips have
mean-square cost proportional to their multiplicative width. -/
theorem mrt_boundary_mean_square (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hb : ∀ n ∈ mrtBoundarySet N δ, ‖b n‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial (mrtBoundarySet N δ)
      (fun n => b n / (n : ℂ)) (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      96 * Real.exp 1 * (T / (N : ℝ) + 1) * (δ - 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrange : mrtBoundarySet N δ ⊆ Ioc 0 (4 * N) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mrt_boundary_range hN hδ2 hn
    exact mem_Ioc.mpr ⟨by omega, hn2⟩
  have hcoeff : (∑ n ∈ mrtBoundarySet N δ, ‖b n / (n : ℂ)‖ ^ 2) ≤
      3 * (δ - 1) / (N : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ mrtBoundarySet N δ, (1 / (N : ℝ)) ^ 2 := by
        apply sum_le_sum
        intro n hn
        rw [norm_div, Complex.norm_natCast]
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div₀ (by norm_num) (hb n hn) hNr
          (by exact_mod_cast (mrt_boundary_range hN hδ2 hn).1.le)
      _ = ((mrtBoundarySet N δ).card : ℝ) * (1 / (N : ℝ)) ^ 2 := by simp
      _ ≤ (3 * (δ - 1) * N) * (1 / (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (mrt_boundary_card N hδ) (by positivity)
      _ = _ := by field_simp
  apply (mrt_dirichlet_mean_square_subset (mrtBoundarySet N δ) hrange
    (fun n => b n / (n : ℂ)) hT).trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + (4 * N : ℕ)) * (3 * (δ - 1) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = 24 * Real.exp 1 * (T / (N : ℝ) + 4) * (δ - 1) := by
      push_cast
      field_simp; ring
    _ ≤ _ := by
      have hd : 0 ≤ Real.exp 1 * (δ - 1) := mul_nonneg (Real.exp_pos _).le (by linarith)
      have ht := mul_nonneg (div_nonneg hT.le hNr.le) hd
      nlinarith

end TwoPointCorrelations

end OAI
