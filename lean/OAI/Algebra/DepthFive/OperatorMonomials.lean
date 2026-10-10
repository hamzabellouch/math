import OAI.Algebra.DepthFive.MixedOperator
import OAI.Algebra.DepthFive.IteratedDerivative

namespace OAI

noncomputable section

namespace Problem335

open MvPolynomial
open scoped BigOperators

variable {K σ : Type*} [CommSemiring K]

/-- Exponents of the variables acting by differentiation. -/
def derivExponent (isV : σ → Bool) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.filter fun i => isV i = true

/-- Exponents of the variables acting by multiplication. -/
def mulExponent (isV : σ → Bool) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.filter fun i => isV i = false

/-- Integral coefficient supplied by a mixed derivative on a monomial. -/
def operatorFactorial (isV : σ → Bool) (d e : σ →₀ ℕ) : ℕ :=
  d.prod fun i k => if isV i then (e i).descFactorial k else 1

theorem variableOperator_pow_true_monomial (isV : σ → Bool) (i : σ)
    (hi : isV i = true) (k : ℕ) (e : σ →₀ ℕ) (b : K) :
    (variableOperator isV i ^ k) (monomial e b) =
      monomial (e - Finsupp.single i k) (b * (e i).descFactorial k) := by
  simpa [variableOperator, hi, Module.End.coe_pow] using
    iterate_pderiv_monomial i k e b

theorem variableOperator_pow_false_monomial (isV : σ → Bool) (i : σ)
    (hi : isV i = false) (k : ℕ) (e : σ →₀ ℕ) (b : K) :
    (variableOperator isV i ^ k) (monomial e b) =
      monomial (Finsupp.single i k + e) b := by
  simp [variableOperator, hi, LinearMap.pow_mulLeft, X_pow_eq_monomial]

theorem operatorFactorial_single_add (isV : σ → Bool) (i : σ) (k : ℕ)
    (d e : σ →₀ ℕ) (hi : i ∉ d.support) :
    operatorFactorial isV (Finsupp.single i k + d) e =
      (if isV i then (e i).descFactorial k else 1) * operatorFactorial isV d e := by
  classical
  unfold operatorFactorial
  rw [Finsupp.prod_add_index_of_disjoint]
  · rw [Finsupp.prod_single_index]
    cases isV i <;> simp
  · exact Finset.disjoint_left.mpr fun j hj hd => hi <| by
      have hji : j = i := Finset.mem_singleton.mp (Finsupp.support_single_subset hj)
      simpa [hji] using hd

/-- The complete mixed operator sends a monomial to a single monomial. -/
theorem mixedOperator_monomial_one_apply (isV : σ → Bool) (d e : σ →₀ ℕ) (b : K) :
    mixedOperator isV (monomial d 1) (monomial e b) =
      monomial (e - derivExponent isV d + mulExponent isV d)
        (b * operatorFactorial isV d e) := by
  classical
  induction d using Finsupp.induction with
  | zero => simp [derivExponent, mulExponent, operatorFactorial, Finsupp.filter_zero]
  | single_add i k d hi hk ih =>
    have hdi : d i = 0 := Finsupp.notMem_support_iff.mp hi
    have hei : (e - derivExponent isV d + mulExponent isV d) i = e i := by
      simp [derivExponent, mulExponent, Finsupp.filter_apply, hdi]
    have hsplit : (monomial (Finsupp.single i k + d) (1 : K)) =
        X i ^ k * monomial d 1 := by
      rw [add_comm, monomial_add_single, mul_comm]
    rw [hsplit, mixedOperator_mul_apply, ih, map_pow, mixedOperator_X,
      operatorFactorial_single_add isV i k d e hi]
    cases hvi : isV i
    · rw [variableOperator_pow_false_monomial isV i hvi]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      have hdv : derivExponent isV (Finsupp.single i k + d) = derivExponent isV d := by
        simp [derivExponent, Finsupp.filter_add, Finsupp.filter_single_of_neg, hvi]
      have hdu : mulExponent isV (Finsupp.single i k + d) =
          Finsupp.single i k + mulExponent isV d := by
        simp [mulExponent, Finsupp.filter_add, Finsupp.filter_single_of_pos, hvi]
      rw [hdv, hdu]
      congr 1
      ac_rfl
    · rw [variableOperator_pow_true_monomial isV i hvi, hei]
      simp only [↓reduceIte, Nat.cast_mul]
      have hdv : derivExponent isV (Finsupp.single i k + d) =
          Finsupp.single i k + derivExponent isV d := by
        simp [derivExponent, Finsupp.filter_add, Finsupp.filter_single_of_pos, hvi]
      have hdu : mulExponent isV (Finsupp.single i k + d) = mulExponent isV d := by
        simp [mulExponent, Finsupp.filter_add, Finsupp.filter_single_of_neg, hvi]
      rw [hdv, hdu]
      have hexp : (e - derivExponent isV d + mulExponent isV d) - Finsupp.single i k =
          e - (Finsupp.single i k + derivExponent isV d) + mulExponent isV d := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [derivExponent, mulExponent, hvi, hdi]
        · simp [hji]
      rw [hexp]
      congr 1
      ring

/-- Exact arbitrary-coefficient monomial action, over every commutative semiring. -/
theorem mixedOperator_monomial_apply (isV : σ → Bool) (d e : σ →₀ ℕ) (a b : K) :
    mixedOperator isV (monomial d a) (monomial e b) =
      monomial (e - derivExponent isV d + mulExponent isV d)
        (a * b * operatorFactorial isV d e) := by
  have h : monomial d a = C a * monomial d 1 := by rw [C_mul_monomial, mul_one]
  rw [h, mixedOperator_mul_apply, mixedOperator_monomial_one_apply, mixedOperator_C]
  simp [smul_monomial, smul_eq_mul, mul_assoc]

/-- All matrix coefficients of a monomial mixed operator are explicit integral multiples. -/
theorem coeff_mixedOperator_monomial [DecidableEq σ] (isV : σ → Bool) (d e f : σ →₀ ℕ) (a b : K) :
    (mixedOperator isV (monomial d a) (monomial e b)).coeff f =
      if e - derivExponent isV d + mulExponent isV d = f
      then a * b * operatorFactorial isV d e else 0 := by
  classical
  rw [mixedOperator_monomial_apply, coeff_monomial]

/-- A mixed monomial has nonzero integral multiplier exactly when differentiation is possible. -/
theorem operatorFactorial_ne_zero_iff (isV : σ → Bool) (d e : σ →₀ ℕ) :
    operatorFactorial isV d e ≠ 0 ↔ derivExponent isV d ≤ e := by
  classical
  unfold operatorFactorial
  rw [Finsupp.prod_ne_zero_iff]
  constructor
  · intro h i
    cases hvi : isV i
    · simp [derivExponent, hvi]
    · have hle : d i ≤ e i := by
        by_cases hdi : d i = 0
        · simp [hdi]
        · have hn := h i (Finsupp.mem_support_iff.mpr hdi)
          simpa [hvi, Nat.descFactorial_eq_zero_iff_lt, not_lt] using hn
      simpa [derivExponent, Finsupp.filter_apply, hvi] using hle
  · intro h i hi
    cases hvi : isV i
    · simp
    · have hle := h i
      simpa [derivExponent, Finsupp.filter_apply, hvi,
        Nat.descFactorial_eq_zero_iff_lt, not_lt] using hle

/-- Over characteristic zero without zero divisors, the only possible vanishing is
an excessive differentiation exponent or a zero input coefficient. -/
theorem mixedOperator_monomial_ne_zero_iff [NoZeroDivisors K] [CharZero K]
    (isV : σ → Bool) (d e : σ →₀ ℕ) (a b : K) :
    mixedOperator isV (monomial d a) (monomial e b) ≠ 0 ↔
      a ≠ 0 ∧ b ≠ 0 ∧ derivExponent isV d ≤ e := by
  rw [mixedOperator_monomial_apply]
  simp [operatorFactorial_ne_zero_iff, and_assoc]

/-- The action of an arbitrary polynomial on a monomial is an explicit finite sum. -/
theorem mixedOperator_apply_monomial (isV : σ → Bool) (p : MvPolynomial σ K)
    (e : σ →₀ ℕ) (b : K) :
    mixedOperator isV p (monomial e b) =
      ∑ d ∈ p.support, monomial (e - derivExponent isV d + mulExponent isV d)
        (p.coeff d * b * operatorFactorial isV d e) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum, LinearMap.sum_apply]
  simp only [mixedOperator_monomial_apply]

/-- Distinct non-annihilated operator monomials have distinct output exponents
on each fixed source monomial. This is the orthogonality behind the first trace. -/
theorem operator_target_injective (isV : σ → Bool) (e d₁ d₂ : σ →₀ ℕ)
    (h₁ : derivExponent isV d₁ ≤ e) (h₂ : derivExponent isV d₂ ≤ e)
    (h : e - derivExponent isV d₁ + mulExponent isV d₁ =
      e - derivExponent isV d₂ + mulExponent isV d₂) : d₁ = d₂ := by
  classical
  ext i
  have heq := DFunLike.congr_fun h i
  have hle₁ := h₁ i
  have hle₂ := h₂ i
  cases hi : isV i <;>
    simp [derivExponent, mulExponent, hi] at heq hle₁ hle₂
  · omega
  · omega

/-- At a surviving monomial's own target, no other operator monomial contributes. -/
theorem coeff_mixedOperator_at_target (isV : σ → Bool) (p : MvPolynomial σ K)
    (d e : σ →₀ ℕ) (b : K) (hd : derivExponent isV d ≤ e) :
    (mixedOperator isV p (monomial e b)).coeff
      (e - derivExponent isV d + mulExponent isV d) =
      p.coeff d * b * operatorFactorial isV d e := by
  classical
  rw [mixedOperator_apply_monomial, coeff_sum]
  rw [Finset.sum_eq_single d]
  · simp
  · intro f hf hfd
    by_cases hfe : derivExponent isV f ≤ e
    · have hne : e - derivExponent isV f + mulExponent isV f ≠
          e - derivExponent isV d + mulExponent isV d := by
        intro heq
        exact hfd (operator_target_injective isV e f d hfe hd heq)
      simp [coeff_monomial, hne]
    · have hz : operatorFactorial isV f e = 0 := by
        by_contra h
        exact hfe ((operatorFactorial_ne_zero_iff isV f e).mp h)
      simp [hz]
  · intro hnot
    have hc : p.coeff d = 0 := notMem_support_iff.mp hnot
    simp [hc]

end Problem335

end

end OAI
