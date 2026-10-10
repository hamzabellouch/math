import OAI.NumberTheory.TwoPointCorrelations.MRTCoarseBins
import OAI.NumberTheory.TwoPointCorrelations.MRTRamareMeanError

namespace OAI

/-! The literal coarse-bin polynomial differs from the supported dyadic
polynomial by the prime-square correction and the two short boundary
strips.  Both errors are estimated before any sum over prime bins. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtWeightedRamareCoefficient (P : Finset ℕ) (F : ℕ → ℂ)
    (n : ℕ) : ℂ := F n * ((∑ p ∈ P, mrtRamareWeight P n p : ℝ) : ℂ)

noncomputable def mrtCoarsePolynomial (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) (F : ℕ → ℂ) (t : ℝ) : ℂ :=
  mrtExponentialPolynomial (Ioc 0 (4 * N))
    (fun n => F n * (mrtCoarseRamareWeight P L N n : ℂ) / (n : ℂ))
    (fun n => -Real.log (n : ℝ)) t

noncomputable def mrtCoarseBoundaryPolynomial (P : Finset ℕ) (L : ℕ → ℝ)
    (N : ℕ) (δ : ℝ) (F : ℕ → ℂ) (t : ℝ) : ℂ :=
  mrtExponentialPolynomial (mrtBoundarySet N δ)
    (fun n => F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ) / (n : ℂ))
    (fun n => -Real.log (n : ℝ)) t

lemma mrt_dyadic_polynomial_extend (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    mrtDyadicPolynomial b N t =
      mrtExponentialPolynomial (Ioc 0 (4 * N))
        (fun n => (if N < n ∧ n ≤ 2 * N then b n else 0) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  calc
    _ = ∑ n ∈ Ioc N (2 * N),
        ((if N < n ∧ n ≤ 2 * N then b n else 0) / (n : ℂ)) *
          Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
      apply sum_congr rfl
      intro n hn
      rw [ite_eq_left (mem_Ioc.mp hn)]
    _ = _ := by
      apply sum_subset
      · intro n hn
        have hn' := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨by omega, by omega⟩
      · intro n _ hn
        simp only [mem_Ioc] at hn
        rw [ite_eq_right hn, zero_div, zero_mul]

/-- Exact boundary identity, with the original and coarse polynomials
both retaining their actual numerical coefficients. -/
theorem mrt_coarse_boundary_identity (P : Finset ℕ) (L : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F : ℕ → ℂ) (t : ℝ) :
    mrtDyadicPolynomial (mrtWeightedRamareCoefficient P F) N t -
        mrtCoarsePolynomial P L N F t =
      mrtCoarseBoundaryPolynomial P L N δ F t := by
  rw [mrt_dyadic_polynomial_extend]
  unfold mrtCoarsePolynomial mrtCoarseBoundaryPolynomial mrtExponentialPolynomial
  rw [← sum_sub_distrib]
  calc
    _ = ∑ n ∈ Ioc 0 (4 * N),
        (F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ) / (n : ℂ)) *
          Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
      apply sum_congr rfl
      intro n _
      unfold mrtWeightedRamareCoefficient mrtCoarseBoundaryCoefficient
      by_cases hn : N < n ∧ n ≤ 2 * N
      · simp only [ite_eq_left hn, Complex.ofReal_sub]
        ring
      · simp only [ite_eq_right hn, Complex.ofReal_sub, Complex.ofReal_zero]
        ring
    _ = _ := by
      symm
      apply sum_subset
      · intro n hn
        obtain ⟨hn1, hn2⟩ := mrt_boundary_range hN hδ2 hn
        exact mem_Ioc.mpr ⟨by omega, hn2⟩
      · intro n _ hn
        dsimp only
        rw [mrt_coarse_boundary_support P L N n hδ hL hn,
          Complex.ofReal_zero, mul_zero, zero_div, zero_mul]

lemma mrt_coarse_boundary_coefficient_norm (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) (N : ℕ)
    (F : ℕ → ℂ) (hF : OneBounded F) {n : ℕ} (hn : 0 < n) :
    ‖F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul (hF n hn) (mrt_coarse_boundary_abs P hP L N n)
    (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem mrt_coarse_boundary_mean (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (F : ℕ → ℂ) (hF : OneBounded F) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtCoarseBoundaryPolynomial P L N δ F t‖ ^ 2) ≤
      96 * Real.exp 1 * (T / (N : ℝ) + 1) * (δ - 1) := by
  apply mrt_boundary_mean_square
    (fun n => F n * (mrtCoarseBoundaryCoefficient P L N n : ℂ)) hN hδ hδ2 _ hT
  intro n hn
  exact mrt_coarse_boundary_coefficient_norm P hP L N F hF
    (hN.trans (mrt_boundary_range hN hδ2 hn).1)

lemma mrt_weighted_ramare_sum (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    (∑ p ∈ P, if p ∣ n then
      F n / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) =
      mrtWeightedRamareCoefficient P F n := by
  unfold mrtWeightedRamareCoefficient
  rw [Complex.ofReal_sum, mul_sum]
  apply sum_congr rfl
  intro p _
  unfold mrtRamareWeight
  by_cases hp : p ∣ n
  · simp only [hp, ite_true, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast]
    ring
  · simp only [hp, ite_false, Complex.ofReal_zero, mul_zero]

noncomputable def mrtSupportedCoefficient (P : Finset ℕ) (F : ℕ → ℂ)
    (n : ℕ) : ℂ := if finitePrimeDivisorCount P n = 0 then 0 else F n

lemma mrt_supported_ramare_split (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    mrtSupportedCoefficient P F n =
      mrtRamareCorrection P F n + mrtWeightedRamareCoefficient P F n := by
  unfold mrtSupportedCoefficient mrtRamareCorrection
  rw [mrt_weighted_ramare_sum]
  ring

lemma mrt_dyadic_polynomial_add (a b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    mrtDyadicPolynomial (fun n => a n + b n) N t =
      mrtDyadicPolynomial a N t + mrtDyadicPolynomial b N t := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  simp only [add_div, add_mul, sum_add_distrib]

theorem mrt_coarse_error_identity (P : Finset ℕ) (L : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F : ℕ → ℂ) (t : ℝ) :
    mrtDyadicPolynomial (mrtSupportedCoefficient P F) N t -
        mrtCoarsePolynomial P L N F t =
      mrtDyadicPolynomial (mrtRamareCorrection P F) N t +
        mrtCoarseBoundaryPolynomial P L N δ F t := by
  have hs : mrtSupportedCoefficient P F =
      fun n => mrtRamareCorrection P F n + mrtWeightedRamareCoefficient P F n :=
    funext (mrt_supported_ramare_split P F)
  rw [hs, mrt_dyadic_polynomial_add]
  rw [← mrt_coarse_boundary_identity P L hN hδ hδ2 hL F t]
  ring

/-- Coarse-bin decoupling costs the reciprocal square mass and the bin
width.  There is no loss depending on the number of bins. -/
theorem mrt_coarse_error_mean_square (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P, L p ≤ p ∧ (p : ℝ) ≤ δ * L p)
    (F : ℕ → ℂ) (hF : OneBounded F) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtSupportedCoefficient P F) N t -
      mrtCoarsePolynomial P L N F t‖ ^ 2) ≤
      192 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) := by
  let A := mrtDyadicPolynomial (mrtRamareCorrection P F) N
  let B := mrtCoarseBoundaryPolynomial P L N δ F
  have hA : Continuous A := mrtExponentialPolynomial_continuous _ _ _
  have hB : Continuous B := mrtExponentialPolynomial_continuous _ _ _
  have ha : IntervalIntegrable (fun t => ‖A t‖ ^ 2) volume (-T) T :=
    (hA.norm.pow 2).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun t => ‖B t‖ ^ 2) volume (-T) T :=
    (hB.norm.pow 2).intervalIntegrable _ _
  have hab : IntervalIntegrable (fun t => ‖A t + B t‖ ^ 2) volume (-T) T :=
    ((hA.add hB).norm.pow 2).intervalIntegrable _ _
  have hmajor : (∫ t in -T..T, ‖A t + B t‖ ^ 2) ≤
      2 * (∫ t in -T..T, ‖A t‖ ^ 2) + 2 * (∫ t in -T..T, ‖B t‖ ^ 2) := by
    calc
      _ ≤ ∫ t in -T..T, (2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2) := by
        apply intervalIntegral.integral_mono_on (by linarith : -T ≤ T) hab
          ((ha.const_mul 2).add (hb.const_mul 2))
        intro t _
        have hh := norm_add_le (A t) (B t)
        nlinarith [sq_nonneg (‖A t‖ - ‖B t‖), norm_nonneg (A t + B t),
          norm_nonneg (A t), norm_nonneg (B t)]
      _ = _ := by
        rw [intervalIntegral.integral_add (ha.const_mul 2) (hb.const_mul 2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp_rw [mrt_coarse_error_identity P L hN hδ hδ2 hL F]
  change (∫ t in -T..T, ‖A t + B t‖ ^ 2) ≤ _
  apply hmajor.trans
  have hma := mrt_ramare_correction_mean_square P hP F hF hN hT
  have hmb := mrt_coarse_boundary_mean P hP L hN hδ hδ2 F hF hT
  change (∫ t in -T..T, ‖A t‖ ^ 2) ≤ _ at hma
  change (∫ t in -T..T, ‖B t‖ ^ 2) ≤ _ at hmb
  have hc : 0 ≤ Real.exp 1 * (T / (N : ℝ) + 1) := by positivity
  have hs : 0 ≤ (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
      (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 := by positivity
  nlinarith

end TwoPointCorrelations

end OAI
