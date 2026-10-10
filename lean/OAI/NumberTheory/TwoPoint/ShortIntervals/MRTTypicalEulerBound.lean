import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothTypical
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothDistance

namespace OAI

/-! The exact typical smooth Euler product retains half of the full
pretentious-distance exponent, independently of the number of bands. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped Classical

theorem mrt_typical_smooth_euler_bound {ι : Type*} (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, P j ⊆ primesUpTo N) (hdis : Set.PairwiseDisjoint (J : Set ι) P) :
    ‖∑' n : Nat.smoothNumbers (N + 1),
      if mrtTypical J P n then LSeries.term F (1 + (t : ℂ) * Complex.I) n else 0‖ ≤
      Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance F (mrtArchimedeanTwist t) N / 2 +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
  let z : ℕ → ℂ := mrtPrimeEulerTerm F t
  have hz (p : ℕ) (hp : p ∈ primesUpTo N) : ‖z p‖ ≤ 1 / 2 := by
    have hprime : p.Prime := (mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    exact (mrtPrimeEulerTerm_norm_le F t hprime.pos (hFb p hprime.pos)).trans
      (one_div_le_one_div_of_le (by norm_num) hp2)
  rw [(mrt_typical_smooth_euler F hF1 hF hFb N t J P hP hdis).tsum_eq]
  have he := mrt_partitioned_euler_bound (primesUpTo N) J P z hP hdis hz
  apply he.trans
  have hmass : (∑ p ∈ primesUpTo N, (‖z p‖ + ‖z p‖ ^ 2)) ≤
      (∑ p ∈ primesUpTo N, (1 : ℝ) / p) +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2
    have hn := mrtPrimeEulerTerm_norm_le F t hprime.pos (hFb p hprime.pos)
    apply add_le_add hn
    simpa only [one_div, inv_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hfull := mrt_finite_euler_distance_bound F hFb t N
  calc
    _ ≤ Real.sqrt (Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
          squaredDistance F (mrtArchimedeanTwist t) N +
          ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2)) *
        Real.exp (((∑ p ∈ primesUpTo N, (1 : ℝ) / p) +
          ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) / 2) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hfull)
        (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hmass (by norm_num)))
        (Real.exp_pos _).le (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← Real.exp_half, ← Real.exp_add]
      congr 1
      ring

/-- The absolute constant does not depend on the number or positions of
the disjoint prime bands. -/
theorem mrt_typical_smooth_distance_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (F : ℕ → ℂ), F 1 = 1 →
      (∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n) → OneBounded F →
      ∀ (N : ℕ), 2 ≤ N → ∀ (t : ℝ) {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, P j ⊆ primesUpTo N) → Set.PairwiseDisjoint (J : Set ι) P →
      ‖∑' n : Nat.smoothNumbers (N + 1),
        if mrtTypical J P n then LSeries.term F (1 + (t : ℂ) * Complex.I) n else 0‖ ≤
        C * Real.log N * Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N / 2) := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  refine ⟨Real.exp (C + 2), Real.exp_pos _, ?_⟩
  intro F hF1 hF hFb N hN t ι J P hP hdis
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hm := hC (N : ℝ) hN2
  rw [mrt_sievePrimesUpTo_nat] at hm
  have hmass := (abs_le.mp hm).2
  have hsq := mrt_prime_inverse_square_sum N
  calc
    _ ≤ Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance F (mrtArchimedeanTwist t) N / 2 +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) :=
      mrt_typical_smooth_euler_bound F hF1 hF hFb N t J P hP hdis
    _ ≤ Real.exp (C + 2 + Real.log (Real.log N) +
        (-squaredDistance F (mrtArchimedeanTwist t) N / 2)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log hlog]

end TwoPointCorrelations

end OAI
