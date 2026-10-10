import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszSeries
import OAI.NumberTheory.TwoPoint.Halasz.HalaszSparseSmallPrimes

namespace OAI

/-! The exact sparse-prime input follows from the quadratic Riesz-Mangoldt
kernel. This finite bridge retains the published error and arbitrary Y. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def mrtRieszPrimeWeight (Y : ℝ) (n : ℕ) : ℝ :=
  4 * (max (1 - (n : ℝ) / (4 * Y)) 0) ^ 2

noncomputable def mrtRieszPrimeSupport (Y : ℝ) : Finset ℕ := Icc 1 ⌊4 * Y⌋₊

lemma mrt_riesz_prime_weight_nonneg (Y : ℝ) (n : ℕ) : 0 ≤ mrtRieszPrimeWeight Y n := by
  unfold mrtRieszPrimeWeight
  positivity

lemma mrt_riesz_prime_support {Y : ℝ} (hY : 2 ≤ Y) {p : ℕ}
    (hp : p.Prime) (hpY : (p : ℝ) ≤ 2 * Y) : p ∈ mrtRieszPrimeSupport Y := by
  apply mem_Icc.mpr
  refine ⟨hp.one_le, (Nat.le_floor_iff (by linarith : 0 ≤ 4 * Y)).mpr ?_⟩
  linarith

lemma mrt_riesz_prime_weight_ge_one {Y : ℝ} (hY : 2 ≤ Y) {p : ℕ}
    (hpY : (p : ℝ) ≤ 2 * Y) : 1 ≤ mrtRieszPrimeWeight Y p := by
  have hY0 : 0 < Y := by linarith
  have hr : (p : ℝ) / (4 * Y) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Y)).mpr
    linarith
  have hm : 1 / 2 ≤ max (1 - (p : ℝ) / (4 * Y)) 0 :=
    le_trans (by linarith) (le_max_left _ _)
  unfold mrtRieszPrimeWeight
  nlinarith [sq_nonneg (max (1 - (p : ℝ) / (4 * Y)) 0 - 1 / 2)]

/-- Only the smoothed arithmetic kernel is left by the finite duality step.
The small-logY range has already been proved from Chebyshev. -/
theorem mrt_sparse_prime_of_riesz_kernel
    (hkernel : ∃ C L₀ : ℝ, 0 < C ∧ ∀ L Y : ℝ, L₀ ≤ L → 1 ≤ L → 2 ≤ Y →
      2 * L ^ (3 / 4 : ℝ) * Real.log L < Real.log Y →
      ∀ u : ℝ, |u| ≤ 2 * Real.exp L →
      ‖mrtExponentialPolynomial (mrtRieszPrimeSupport Y)
        (fun n => (mrtRieszPrimeWeight Y n * ArithmeticFunction.vonMangoldt n : ℝ))
        (fun n => -Real.log (n : ℝ)) u‖ ≤
          C * Y / (1 + u ^ 2) + C * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2) :
    HalaszPrimeSparseInput := by
  obtain ⟨C, L₀, hC, hk⟩ := hkernel
  let D := 2 * Real.log 4 + 8 * C
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, L₀, hD, ?_⟩
  intro L Y hL₀ hL hY P hP a S hheight hsep
  have hmass : 0 ≤ ∑ p ∈ P, ‖a p‖ ^ 2 / Real.log (p : ℝ) := by
    apply sum_nonneg
    intro p hp
    apply div_nonneg (sq_nonneg _)
    exact Real.log_nonneg (by exact_mod_cast (hP p hp).1.one_le)
  have hE : 0 ≤ Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2 := by positivity
  have hY0 : 0 ≤ Y := by linarith
  have hfactor : 0 ≤ Y + (S.card : ℝ) * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2 := by
    positivity
  by_cases hs : Real.log Y ≤ 2 * L ^ (3 / 4 : ℝ) * Real.log L
  · apply (halasz_sparse_small_primes hL hY hs P hP a S hsep).trans
    apply mul_le_mul_of_nonneg_right _ hmass
    exact mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) hfactor
  · have hPK : P ⊆ mrtRieszPrimeSupport Y := by
      intro p hp
      exact mrt_riesz_prime_support hY (hP p hp).1 (hP p hp).2.2
    have hh := mrt_sparse_prime_gram (mrtRieszPrimeSupport Y) P hPK
      (fun p hp => (hP p hp).1) (mrtRieszPrimeWeight Y)
      (fun n _ => mrt_riesz_prime_weight_nonneg Y n)
      (fun p hp => mrt_riesz_prime_weight_ge_one hY (hP p hp).2.2)
      a S hsep (A := C * Y)
      (D := C * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2)
      (by positivity) (by positivity) (fun t ht s hs' => hk L Y hL₀ hL hY
        (lt_of_not_ge hs) (t - s) (by
          have hr := abs_sub t s
          linarith [hheight t ht, hheight s hs']))
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ hmass
    calc
      _ ≤ (8 * C) * (Y + (S.card : ℝ) * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2) := by
        nlinarith [mul_nonneg (show 0 ≤ 7 * C by positivity)
          (show 0 ≤ (S.card : ℝ) * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2 by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]) hfactor

end TwoPointCorrelations

end OAI
