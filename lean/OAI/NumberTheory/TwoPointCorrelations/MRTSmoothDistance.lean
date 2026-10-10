import OAI.NumberTheory.TwoPointCorrelations.MRTSmoothEuler
import OAI.NumberTheory.TwoPointCorrelations.PrimeReciprocalTheorem
import Mathlib.Analysis.PSeries

namespace OAI

/-! Mertens turns the exact smooth Euler product into the usual
`log N * exp(-distance)` estimate, uniformly in the bounded coefficient. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_sievePrimesUpTo_nat (N : ℕ) : sievePrimesUpTo (N : ℝ) = primesUpTo N := by
  ext p
  simp only [sievePrimesUpTo, primesUpTo, mem_filter, mem_Iic, Nat.floor_natCast,
    mem_range, Nat.lt_succ_iff]

lemma mrt_prime_inverse_square_sum (N : ℕ) :
    (∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  have hs : primesUpTo N ⊆ Ioo 0 (N + 1) := by
    intro p hp
    exact mem_Ioo.mpr ⟨(mem_filter.mp hp).2.pos, mem_range.mp (mem_filter.mp hp).1⟩
  calc
    _ ≤ ∑ n ∈ Ioo 0 (N + 1), ((n : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ ≤ 2 := by simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))

/-- The absolute Euler-product constant is independent of the
coefficient, height and smooth cutoff. -/
theorem mrt_smooth_distance_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (F : ℕ → ℂ), F 1 = 1 →
      (∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n) → OneBounded F →
      ∀ (N : ℕ), 2 ≤ N → ∀ t : ℝ,
      ‖∑' n : Nat.smoothNumbers (N + 1), LSeries.term F (1 + (t : ℂ) * Complex.I) n‖ ≤
        C * Real.log N * Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N) := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  refine ⟨Real.exp (C + 2), Real.exp_pos _, ?_⟩
  intro F hF1 hF hFb N hN t
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hm := hC (N : ℝ) hN2
  rw [mrt_sievePrimesUpTo_nat] at hm
  have hmass := (abs_le.mp hm).2
  have hsq := mrt_prime_inverse_square_sum N
  calc
    _ ≤ Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance F (mrtArchimedeanTwist t) N +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) :=
      mrt_smooth_euler_distance_bound F hF1 hF hFb N t
    _ ≤ Real.exp (C + 2 + Real.log (Real.log N) +
        (-squaredDistance F (mrtArchimedeanTwist t) N)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log hlog]

end TwoPointCorrelations

end OAI
