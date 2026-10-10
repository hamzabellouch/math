import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace OAI
/-!
# Vaughan's identity with finite cutoffs

This file supplies an unconditional algebraic input to the analytic three-prime
route. Multiplication of arithmetic functions below is Dirichlet convolution.
No estimate for exponential sums over primes is assumed or asserted here.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- The part of an arithmetic function supported on integers at most `U`. -/
def shortPart {R : Type*} [Zero R] (U : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- The complementary part, supported on integers strictly above `U`. -/
def longPart {R : Type*} [Zero R] (U : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] lemma shortPart_apply {R : Type*} [Zero R]
    (U : ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    shortPart U f n = if n ≤ U then f n else 0 := rfl

@[simp] lemma longPart_apply {R : Type*} [Zero R]
    (U : ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    longPart U f n = if U < n then f n else 0 := rfl

lemma shortPart_add_longPart {R : Type*} [AddMonoid R]
    (U : ℕ) (f : ArithmeticFunction R) : shortPart U f + longPart U f = f := by
  ext n
  by_cases hn : n ≤ U <;> simp [hn, Nat.not_lt.mpr, Nat.lt_of_not_ge]

lemma longPart_eq_sub_shortPart {R : Type*} [AddCommGroup R]
    (U : ℕ) (f : ArithmeticFunction R) : longPart U f = f - shortPart U f := by
  have h := shortPart_add_longPart U f
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

/-- Vaughan's four-term identity, valid also at zero and for zero cutoffs.
The first convolution is Type I; the second has a coefficient supported on
`[1,U*V]`; the last is the long-long Type II convolution. -/
theorem vonMangoldt_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      shortPart V ArithmeticFunction.vonMangoldt +
      shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log -
      (shortPart U (μ : ArithmeticFunction ℝ) *
        shortPart V ArithmeticFunction.vonMangoldt) * (ζ : ArithmeticFunction ℝ) +
      (longPart U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
        longPart V ArithmeticFunction.vonMangoldt := by
  rw [longPart_eq_sub_shortPart, longPart_eq_sub_shortPart]
  have hμ : (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hΛ : (ζ : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt =
      ArithmeticFunction.log := ArithmeticFunction.zeta_mul_vonMangoldt
  calc
    ArithmeticFunction.vonMangoldt =
        ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
          ArithmeticFunction.vonMangoldt := by rw [hμ, one_mul]
    _ = _ := by
      rw [← hΛ]
      have hshort : ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
          shortPart V ArithmeticFunction.vonMangoldt =
          shortPart V ArithmeticFunction.vonMangoldt := by rw [hμ, one_mul]
      linear_combination hshort

/-- A convolution of two short parts has the expected product support. -/
lemma shortPart_mul_eq_zero_of_lt {R : Type*} [Semiring R]
    (U V n : ℕ) (f g : ArithmeticFunction R) (hn : U * V < n) :
    (shortPart U f * shortPart V g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  have habn := (Nat.mem_divisorsAntidiagonal.mp hab).1
  by_cases ha : ab.1 ≤ U
  · have hb : ¬ ab.2 ≤ V := by
      intro hb
      have hm := Nat.mul_le_mul ha hb
      rw [habn] at hm
      omega
    simp [ha, hb]
  · simp [ha]

/-- Convolving a long part cannot create a smaller positive index. -/
lemma longPart_mul_eq_zero_of_le {R : Type*} [Semiring R]
    (U n : ℕ) (f g : ArithmeticFunction R) (hn : n ≤ U) :
    (longPart U f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
  have ha : ab.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ⟨ab.2, hprod.symm⟩
  have hnot : ¬ U < ab.1 := by omega
  simp [hnot]

lemma abs_shortPart_le (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    |shortPart U f n| ≤ |f n| := by
  by_cases hn : n ≤ U <;> simp [hn, abs_nonneg]

lemma abs_longPart_le (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    |longPart U f n| ≤ |f n| := by
  by_cases hn : U < n <;> simp [hn, abs_nonneg]

lemma abs_real_moebius_le_one (n : ℕ) :
    |(μ : ArithmeticFunction ℝ) n| ≤ 1 := by
  change |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

/-- The short convolution coefficient appearing in Type I sums. -/
def typeICoefficient (U V : ℕ) : ArithmeticFunction ℝ :=
  shortPart U (μ : ArithmeticFunction ℝ) * shortPart V ArithmeticFunction.vonMangoldt

/-- The coefficient appearing in the long-long Type II sum. -/
def typeIICoefficient (U : ℕ) : ArithmeticFunction ℝ :=
  longPart U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)

lemma typeICoefficient_eq_zero (U V n : ℕ) (hn : U * V < n) :
    typeICoefficient U V n = 0 := shortPart_mul_eq_zero_of_lt U V n _ _ hn

lemma typeIICoefficient_eq_zero (U n : ℕ) (hn : n ≤ U) :
    typeIICoefficient U n = 0 := longPart_mul_eq_zero_of_le U n _ _ hn

/-- The Type I coefficient costs only a logarithm, not a divisor function. -/
lemma abs_typeICoefficient_le_log (U V n : ℕ) :
    |typeICoefficient U V n| ≤ Real.log n := by
  unfold typeICoefficient
  rw [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal,
        |shortPart U (μ : ArithmeticFunction ℝ) ab.1 *
          shortPart V ArithmeticFunction.vonMangoldt ab.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt ab.2 := by
      apply Finset.sum_le_sum
      intro ab hab
      rw [abs_mul]
      have hμ := (abs_shortPart_le U (μ : ArithmeticFunction ℝ) ab.1).trans
        (abs_real_moebius_le_one ab.1)
      have hΛ := abs_shortPart_le V ArithmeticFunction.vonMangoldt ab.2
      rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] at hΛ
      calc
        _ ≤ 1 * ArithmeticFunction.vonMangoldt ab.2 :=
          mul_le_mul hμ hΛ (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    _ = Real.log n := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ b => ArithmeticFunction.vonMangoldt b)]
      exact ArithmeticFunction.vonMangoldt_sum

lemma typeIICoefficient_apply (U n : ℕ) :
    typeIICoefficient U n =
      ∑ d ∈ n.divisors.filter (U < ·), (μ : ArithmeticFunction ℝ) d := by
  rw [typeIICoefficient, ArithmeticFunction.coe_mul_zeta_apply]
  simp only [longPart_apply, Finset.sum_filter]

/-- A uniform elementary coefficient bound for the Type II sum. -/
lemma abs_typeIICoefficient_le_divisors_card (U n : ℕ) :
    |typeIICoefficient U n| ≤ (n.divisors.card : ℝ) := by
  rw [typeIICoefficient, ArithmeticFunction.coe_mul_zeta_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors, |longPart U (μ : ArithmeticFunction ℝ) d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact (abs_longPart_le U (μ : ArithmeticFunction ℝ) d).trans
        (abs_real_moebius_le_one d)
    _ = _ := by simp

end Problem337.Vaughan

end

end OAI
