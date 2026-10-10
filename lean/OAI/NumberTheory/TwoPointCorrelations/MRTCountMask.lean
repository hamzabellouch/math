import OAI.NumberTheory.TwoPointCorrelations.MRTTypicalFactors
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! Reciprocal prime-count weights as an integral of multiplicative
soft masks.  This is the exact cofactor-weight reduction used in MRT
Appendix A, Lemma A.5. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtCountMask (P : Finset ℕ) (u : ℝ) (n : ℕ) : ℝ :=
  u ^ finitePrimeDivisorCount P n

lemma finitePrimeDivisorCount_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    finitePrimeDivisorCount P 1 = 0 := by
  unfold finitePrimeDivisorCount
  apply sum_eq_zero
  intro p hp
  apply ite_eq_right
  intro hd
  exact (hP p hp).ne_one (Nat.eq_one_of_dvd_one hd)

lemma mrtCountMask_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (u : ℝ) :
    mrtCountMask P u 1 = 1 := by
  simp only [mrtCountMask, finitePrimeDivisorCount_one P hP, pow_zero]

lemma mrtCountMask_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : ℝ) (m n : ℕ) (hcop : m.Coprime n) :
    mrtCountMask P u (m * n) = mrtCountMask P u m * mrtCountMask P u n := by
  simp only [mrtCountMask, finitePrimeDivisorCount_mul P hP m n hcop, pow_add]

lemma mrtCountMask_bounds (P : Finset ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    0 ≤ mrtCountMask P u n ∧ mrtCountMask P u n ≤ 1 :=
  ⟨pow_nonneg hu _, pow_le_one₀ hu hu1⟩

lemma mrtCountMask_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : ℝ) {p : ℕ} (hp : p.Prime) :
    mrtCountMask P u p = if p ∈ P then u else 1 := by
  by_cases hpP : p ∈ P
  · have hnot : ¬p ∣ 1 := fun hd => hp.ne_one (Nat.eq_one_of_dvd_one hd)
    have hc := mrt_prime_divisor_count_mul P hP hpP 1
    simp only [mul_one, hnot, ite_false, finitePrimeDivisorCount_one P hP,
      add_zero] at hc
    simp only [mrtCountMask, hc, pow_one, hpP, ite_true]
  · simp only [mrtCountMask, finitePrimeDivisorCount_prime_outside P hP hp hpP,
      pow_zero, hpP, ite_false]

noncomputable def mrtCountMaskedCoefficient (F : ℕ → ℂ) (P : Finset ℕ)
    (u : ℝ) (n : ℕ) : ℂ := F n * (mrtCountMask P u n : ℂ)

lemma Multiplicative.mrtCountMaskedCoefficient {F : ℕ → ℂ} (hF : Multiplicative F)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (u : ℝ) :
    Multiplicative (mrtCountMaskedCoefficient F P u) := by
  intro m n hm hn hcop
  simp only [TwoPointCorrelations.mrtCountMaskedCoefficient, hF m n hm hn hcop,
    mrtCountMask_mul P hP u m n hcop, Complex.ofReal_mul]
  ring

lemma OneBounded.mrtCountMaskedCoefficient {F : ℕ → ℂ} (hF : OneBounded F)
    (P : Finset ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    OneBounded (mrtCountMaskedCoefficient F P u) := by
  intro n hn
  rw [TwoPointCorrelations.mrtCountMaskedCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mrtCountMask_bounds P hu hu1 n).1]
  exact (mul_le_mul (hF n hn) (mrtCountMask_bounds P hu hu1 n).2
    (mrtCountMask_bounds P hu hu1 n).1 zero_le_one).trans_eq (mul_one 1)

lemma mrtCountMask_integral (P : Finset ℕ) (n : ℕ) :
    (∫ u in (0 : ℝ)..1, mrtCountMask P u n) =
      1 / ((finitePrimeDivisorCount P n : ℝ) + 1) := by
  simp [mrtCountMask, integral_pow]

lemma mrtCountMaskedCoefficient_integral (F : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) :
    (∫ u in (0 : ℝ)..1, mrtCountMaskedCoefficient F P u n) =
      F n / ((finitePrimeDivisorCount P n : ℂ) + 1) := by
  simp only [mrtCountMaskedCoefficient, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, mrtCountMask_integral, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_natCast]
  ring

/-- The literal reciprocal-count cofactor polynomial is the average of
the corresponding soft-mask polynomials. -/
theorem mrt_reciprocal_count_polynomial (S P : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ S, a n / ((finitePrimeDivisorCount P n : ℂ) + 1)) =
      ∫ u in (0 : ℝ)..1, ∑ n ∈ S, mrtCountMaskedCoefficient a P u n := by
  have hc (n : ℕ) : Continuous (fun u : ℝ => mrtCountMaskedCoefficient a P u n) := by
    unfold mrtCountMaskedCoefficient mrtCountMask
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun n _ => (hc n).intervalIntegrable _ _)]
  exact sum_congr rfl (fun n _ => (mrtCountMaskedCoefficient_integral a P n).symm)

theorem mrt_reciprocal_count_polynomial_bound (S P : Finset ℕ) (a : ℕ → ℂ)
    (B : ℝ) (hB : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ‖∑ n ∈ S, mrtCountMaskedCoefficient a P u n‖ ≤ B) :
    ‖∑ n ∈ S, a n / ((finitePrimeDivisorCount P n : ℂ) + 1)‖ ≤ B := by
  rw [mrt_reciprocal_count_polynomial]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := B)
    (f := fun u => ∑ n ∈ S, mrtCountMaskedCoefficient a P u n) (fun u hu => by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact hB u hu.1.le hu.2)
  simpa using hb

/-- Every member of the cofactor integral keeps at least half of the
original distance, uniformly in the softening parameter. -/
theorem mrtCountMaskedCoefficient_distance (F twist : ℕ → ℂ) (P : Finset ℕ)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (N : ℕ)
    (hF : ∀ p ∈ primesUpTo N, ‖F p‖ ≤ 1)
    (htwist : ∀ p ∈ primesUpTo N, ‖twist p‖ ≤ 1) :
    squaredDistance F twist N ≤
      2 * squaredDistance (mrtCountMaskedCoefficient F P u) twist N := by
  exact mrt_masked_distance_lower F twist (mrtCountMask P u) N hF htwist
    (fun p _ => mrtCountMask_bounds P hu hu1 p)

/-- Missing-band and reciprocal-count masks are combined before applying
the distance inequality, so there is only one factor-two loss. -/
theorem mrt_missing_count_mask_distance (F twist : ℕ → ℂ) (Q P : Finset ℕ)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (N : ℕ)
    (hF : ∀ p ∈ primesUpTo N, ‖F p‖ ≤ 1)
    (htwist : ∀ p ∈ primesUpTo N, ‖twist p‖ ≤ 1) :
    squaredDistance F twist N ≤ 2 * squaredDistance
      (mrtCountMaskedCoefficient (fun n => F n * (mrtPrimeMask Q n : ℂ)) P u) twist N := by
  have hm (p : ℕ) : 0 ≤ mrtPrimeMask Q p * mrtCountMask P u p ∧
      mrtPrimeMask Q p * mrtCountMask P u p ≤ 1 := by
    have hq := mrtPrimeMask_bounds Q p
    have hp := mrtCountMask_bounds P hu hu1 p
    exact ⟨mul_nonneg hq.1 hp.1,
      (mul_le_mul hq.2 hp.2 hp.1 zero_le_one).trans_eq (mul_one 1)⟩
  have hb := mrt_masked_distance_lower F twist
    (fun n => mrtPrimeMask Q n * mrtCountMask P u n) N hF htwist (fun p _ => hm p)
  convert hb using 1
  congr 2
  funext n
  simp only [mrtCountMaskedCoefficient, Complex.ofReal_mul, mul_assoc]

end TwoPointCorrelations

end OAI
