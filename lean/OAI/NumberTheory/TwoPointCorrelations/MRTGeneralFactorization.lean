import OAI.NumberTheory.TwoPointCorrelations.MRTGeneralPrimeMean

namespace OAI

/-! Exact coarse prime extraction with its prime-square discrepancy.
Only coprime multiplicativity is needed when the discrepancy is bounded. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_prime_cofactor_expansion (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (hδ2 : δ ≤ 2) {p : ℕ} (hp : p ∈ P) (hp0 : 0 < p)
    (A B : ℕ → ℂ) (t : ℝ) :
    mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t =
      ∑ n ∈ Icc 1 (4 * N), if p ∣ n then
        if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
          ((A p * B (n / p)) / (n : ℂ) *
            Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I)) /
              ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
        else 0
      else 0 := by
  let F : ℕ → ℂ := fun n => A p * B (n / p)
  let G : ℕ → ℂ := fun n =>
    if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
      mrtDirichletAtom F n t / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
    else 0
  have he := divisibility_positivePrefix G p (4 * N) hp0
  simp only [positivePrefix_eq_Icc, natDivisibilityIndicator, ite_mul, one_mul, zero_mul] at he
  change _ = ∑ n ∈ Icc 1 (4 * N), if p ∣ n then G n else 0
  rw [he]
  have hrange : Icc 1 (4 * N / p) ⊆ Icc 1 (4 * N) := by
    intro m hm
    exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1,
      (mem_Icc.mp hm).2.trans (Nat.div_le_self _ _)⟩
  have hf (m : ℕ) : F (p * m) = A p * B m := by
    dsimp [F]
    rw [Nat.mul_div_cancel_left m hp0]
  have hexpand : (∑ m ∈ Icc 1 (4 * N / p), G (p * m)) =
      ∑ m ∈ Icc 1 (4 * N), G (p * m) := by
    apply sum_subset hrange
    intro m hm hout
    dsimp only [G]
    rw [Nat.mul_div_cancel_left m hp0]
    apply ite_eq_right
    intro hw
    have hpm := (mrt_coarse_window_support hδ (show (0 : ℝ) ≤ m by positivity)
      (hL p hp).1 (hL p hp).2 rfl hw).2
    have hmul : (p : ℝ) * m ≤ (4 * N : ℕ) := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      push_cast
      nlinarith
    have hnat : p * m ≤ 4 * N := by exact_mod_cast hmul
    exact hout (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,
      (Nat.le_div_iff_mul_le hp0).mpr (by simpa only [Nat.mul_comm] using hnat)⟩)
  rw [hexpand]
  unfold mrtCofactorPolynomial
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  dsimp only [G]
  rw [Nat.mul_div_cancel_left m hp0]
  by_cases hw : (N : ℝ) < L p * m ∧ L p * m ≤ 2 * N
  · rw [ite_eq_left hw, ite_eq_left hw,
      mrt_dirichlet_atom_mul_of_product F A B hp0 (mem_Icc.mp hm).1 (hf m)]
    ring
  · simp only [ite_eq_right hw, mul_zero]

noncomputable def mrtPrimeExtractionError (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) (C A B : ℕ → ℂ) : ℕ → ℂ :=
  mrtPrimeProductError P
    (fun p n => (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N)
    C A B

lemma mrt_prime_extraction_error_zero (P : Finset ℕ) (L : ℕ → ℝ)
    (hL : ∀ p ∈ P, L p ≤ p) (N : ℕ) (C A B : ℕ → ℂ)
    {n : ℕ} (hn : n ≤ N) : mrtPrimeExtractionError P L N C A B n = 0 := by
  unfold mrtPrimeExtractionError mrtPrimeProductError
  apply sum_eq_zero
  intro p hp
  apply ite_eq_right
  rintro ⟨hd, hlo, _⟩
  have hprod : L p * (n / p : ℕ) ≤ (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (hL p hp) (show (0 : ℝ) ≤ (n / p : ℕ) by positivity)
    simpa only [← Nat.cast_mul, Nat.mul_div_cancel' hd] using hh
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  linarith

/-- The exact polynomial identity precedes all norm estimates and keeps
one discrepancy coefficient per integer, rather than per prime bin. -/
theorem mrt_general_prime_factorization (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) (N : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (C A B : ℕ → ℂ) (t : ℝ) :
    mrtCoarsePolynomial P L N C t -
      (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t) =
      mrtExponentialPolynomial (Ioc N (4 * N))
        (fun n => mrtPrimeExtractionError P L N C A B n / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  have hex : (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t) =
      ∑ p ∈ P, ∑ n ∈ Icc 1 (4 * N), if p ∣ n then
        if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
          ((A p * B (n / p)) / (n : ℂ) *
            Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I)) /
              ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
        else 0
      else 0 := by
    apply sum_congr rfl
    intro p hp
    exact mrt_prime_cofactor_expansion P L N hδ hL hδ2 hp (hP p hp).pos A B t
  rw [mrt_coarse_polynomial_prime_sum, hex, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  rw [sum_comm]
  unfold mrtExponentialPolynomial
  calc
    _ = ∑ n ∈ Icc 1 (4 * N),
        (mrtPrimeExtractionError P L N C A B n / (n : ℂ)) *
          Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
      apply sum_congr rfl
      intro n _
      unfold mrtPrimeExtractionError mrtPrimeProductError
      rw [sum_div, sum_mul]
      apply sum_congr rfl
      intro p _
      by_cases hd : p ∣ n
      · by_cases hw : (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N
        · simp only [hd, hw, ite_true, and_self, mrtDirichletAtom]
          ring
        · simp only [hd, hw, ite_true, ite_false, and_false, sub_self, zero_div, zero_mul]
      · simp only [hd, false_and, ite_false, sub_self, zero_div, zero_mul]
    _ = _ := by
      symm
      apply sum_subset
      · intro n hn
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
      · intro n hn hnot
        have hnN : n ≤ N := by
          by_contra h
          exact hnot (mem_Ioc.mpr ⟨by omega, (mem_Icc.mp hn).2⟩)
        dsimp only
        rw [mrt_prime_extraction_error_zero P L (fun p hp => (hL p hp).1) N C A B hnN]
        simp


/-- The coarse prime-product factorization is valid for general
multiplicative coefficients up to the already controlled square error. -/
theorem mrt_general_prime_factorization_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (C A B : ℕ → ℂ) (hC : OneBounded C) (hA : OneBounded A) (hB : OneBounded B)
    (hproduct : ∀ p ∈ P, ∀ m, 0 < m → ¬p ∣ m → C (p * m) = A p * B m)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtCoarsePolynomial P L N C t -
      (∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t)‖ ^ 2) ≤
      512 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2) := by
  simp_rw [mrt_general_prime_factorization P hP L N hδ hδ2 hL C A B]
  apply mrt_prime_square_broad_mean P hP _ hN _ hT
  intro n hn
  exact mrt_prime_product_error_bound P hP _ C A B hC hA hB hproduct
    (hN.trans (mem_Ioc.mp hn).1)

end TwoPointCorrelations

end OAI
