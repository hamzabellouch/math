import OAI.NumberTheory.TwoPointCorrelations.MRTCoarseMean

namespace OAI

/-! Exact factorization of the coarse Ramaré polynomial into short prime
polynomials and cofactor polynomials with fixed multiplicative windows. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtDirichletAtom (F : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  F n / (n : ℂ) * Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I)

noncomputable def mrtCofactorPolynomial (P : Finset ℕ) (F : ℕ → ℂ)
    (N : ℕ) (a t : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 (4 * N),
    if (N : ℝ) < a * m ∧ a * m ≤ 2 * N then
      mrtDirichletAtom F m t / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)
    else 0

lemma mrt_dirichlet_atom_mul_of_product (F A B : ℕ → ℂ)
    {p m : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hF : F (p * m) = A p * B m) (t : ℝ) :
    mrtDirichletAtom F (p * m) t =
      mrtDirichletAtom A p t * mrtDirichletAtom B m t := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : Complex.exp (((-Real.log ((p * m : ℕ) : ℝ)) * t : ℝ) * Complex.I) =
      Complex.exp (((-Real.log (p : ℝ)) * t : ℝ) * Complex.I) *
        Complex.exp (((-Real.log (m : ℝ)) * t : ℝ) * Complex.I) := by
    rw [Nat.cast_mul, Real.log_mul hpR.ne' hmR.ne', neg_add, add_mul,
      Complex.ofReal_add, add_mul, Complex.exp_add]
  unfold mrtDirichletAtom
  rw [hF, Nat.cast_mul, he]
  ring

lemma mrt_dirichlet_atom_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    {p m : ℕ} (hp : 0 < p) (hm : 0 < m) (t : ℝ) :
    mrtDirichletAtom F (p * m) t =
      mrtDirichletAtom F p t * mrtDirichletAtom F m t :=
  mrt_dirichlet_atom_mul_of_product F F F hp hm (hF p m hp hm) t

lemma mrt_coarse_polynomial_prime_sum (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) (F : ℕ → ℂ) (t : ℝ) :
    mrtCoarsePolynomial P L N F t =
      ∑ p ∈ P, ∑ n ∈ Icc 1 (4 * N),
        if p ∣ n then
          if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
            mrtDirichletAtom F n t /
              ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
          else 0
        else 0 := by
  unfold mrtCoarsePolynomial mrtExponentialPolynomial mrtCoarseRamareWeight
  simp only [Complex.ofReal_sum, mul_sum, sum_div, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [show Ioc 0 (4 * N) = Icc 1 (4 * N) by ext n; simp only [mem_Ioc, mem_Icc]; omega]
  apply sum_congr rfl
  intro n _
  unfold mrtRamareWeight mrtDirichletAtom
  by_cases hp : p ∣ n
  · by_cases hw : (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N
    · simp only [ite_eq_left hp, ite_eq_left hw, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
      ring
    · simp only [ite_eq_left hp, ite_eq_right hw, mul_zero, Complex.ofReal_zero,
        zero_mul, zero_div]
  · simp only [ite_eq_right hp, zero_mul, Complex.ofReal_zero, mul_zero, zero_div]

lemma mrt_coarse_polynomial_cofactor_sum (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) (N : ℕ)
    (F : ℕ → ℂ) (t : ℝ) :
    mrtCoarsePolynomial P L N F t =
      ∑ p ∈ P, ∑ m ∈ Icc 1 (4 * N / p),
        if (N : ℝ) < L p * m ∧ L p * m ≤ 2 * N then
          mrtDirichletAtom F (p * m) t /
            ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)
        else 0 := by
  rw [mrt_coarse_polynomial_prime_sum]
  apply sum_congr rfl
  intro p hp
  let G : ℕ → ℂ := fun n =>
    if (N : ℝ) < L p * (n / p : ℕ) ∧ L p * (n / p : ℕ) ≤ 2 * N then
      mrtDirichletAtom F n t / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
    else 0
  have he := divisibility_positivePrefix G p (4 * N) (hP p hp).pos
  simp only [positivePrefix_eq_Icc, natDivisibilityIndicator, ite_mul, one_mul, zero_mul] at he
  change (∑ n ∈ Icc 1 (4 * N), if p ∣ n then G n else 0) = _
  rw [he]
  apply sum_congr rfl
  intro m _
  dsimp only [G]
  rw [Nat.mul_div_cancel_left m (hP p hp).pos]

/-- Each prime has the same cofactor cutoff as the lower endpoint of its
bin.  The extension of its finite range introduces only zero terms. -/
theorem mrt_coarse_polynomial_factorization_of_product (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) (N : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F A B : ℕ → ℂ)
    (hF : ∀ p ∈ P, ∀ m, 0 < m → F (p * m) = A p * B m) (t : ℝ) :
    mrtCoarsePolynomial P L N F t =
      ∑ p ∈ P, mrtDirichletAtom A p t * mrtCofactorPolynomial P B N (L p) t := by
  rw [mrt_coarse_polynomial_cofactor_sum P hP]
  apply sum_congr rfl
  intro p hp
  have hp0 := (hP p hp).pos
  have hrange : Icc 1 (4 * N / p) ⊆ Icc 1 (4 * N) := by
    intro m hm
    exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1,
      (mem_Icc.mp hm).2.trans (Nat.div_le_self _ _)⟩
  calc
    _ = ∑ m ∈ Icc 1 (4 * N),
        if (N : ℝ) < L p * m ∧ L p * m ≤ 2 * N then
          mrtDirichletAtom F (p * m) t /
            ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)
        else 0 := by
      apply sum_subset hrange
      intro m hm hout
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
    _ = _ := by
      unfold mrtCofactorPolynomial
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      by_cases hw : (N : ℝ) < L p * m ∧ L p * m ≤ 2 * N
      · rw [ite_eq_left hw, ite_eq_left hw,
          mrt_dirichlet_atom_mul_of_product F A B hp0 (mem_Icc.mp hm).1
            (hF p hp m (mem_Icc.mp hm).1)]
        ring
      · simp only [ite_eq_right hw, mul_zero]

theorem mrt_coarse_polynomial_factorization (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) (N : ℕ)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n) (t : ℝ) :
    mrtCoarsePolynomial P L N F t =
      ∑ p ∈ P, mrtDirichletAtom F p t * mrtCofactorPolynomial P F N (L p) t :=
  mrt_coarse_polynomial_factorization_of_product P hP L N hδ hδ2 hL F F F
    (fun p hp m hm => hF p m (hP p hp).pos hm) t

/-- Grouping by a finite bin index produces exactly one short prime
polynomial times one fixed-window cofactor polynomial per bin. -/
theorem mrt_coarse_polynomial_bins_of_product {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (bin : ℕ → ι) (hbin : ∀ p ∈ P, bin p ∈ J)
    (lower : ι → ℝ) (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (F A B : ℕ → ℂ)
    (hF : ∀ p ∈ P, ∀ m, 0 < m → F (p * m) = A p * B m) (t : ℝ) :
    mrtCoarsePolynomial P (fun p => lower (bin p)) N F t =
      ∑ j ∈ J,
        mrtExponentialPolynomial (P.filter (fun p => bin p = j))
          (fun p => A p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t *
        mrtCofactorPolynomial P B N (lower j) t := by
  rw [mrt_coarse_polynomial_factorization_of_product P hP _ N hδ hδ2 hL F A B hF]
  rw [← sum_fiberwise_of_maps_to hbin]
  apply sum_congr rfl
  intro j _
  unfold mrtExponentialPolynomial
  rw [sum_mul]
  apply sum_congr rfl
  intro p hp
  have hbp := (mem_filter.mp hp).2
  simp only [mrtDirichletAtom, hbp]

theorem mrt_coarse_polynomial_bins {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (bin : ℕ → ι) (hbin : ∀ p ∈ P, bin p ∈ J)
    (lower : ι → ℝ) (N : ℕ) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n) (t : ℝ) :
    mrtCoarsePolynomial P (fun p => lower (bin p)) N F t =
      ∑ j ∈ J,
        mrtExponentialPolynomial (P.filter (fun p => bin p = j))
          (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t *
        mrtCofactorPolynomial P F N (lower j) t :=
  mrt_coarse_polynomial_bins_of_product J P hP bin hbin lower N hδ hδ2 hL F F F
    (fun p hp m hm => hF p m (hP p hp).pos hm) t

end TwoPointCorrelations

end OAI
