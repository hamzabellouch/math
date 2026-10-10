import OAI.NumberTheory.TwoPoint.Halasz.HalaszNearEnergy
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse

namespace OAI

/-! The near-frequency exceptional set can be controlled in mean square
without paying for the width of that frequency interval. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_dyadic_sub (F G : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    mrtDyadicPolynomial (fun n => F n - G n) N t =
      mrtDyadicPolynomial F N t - mrtDyadicPolynomial G N t := by
  unfold mrtDyadicPolynomial mrtExponentialPolynomial
  simp only [sub_div, sub_mul, sum_sub_distrib]

lemma halasz_exceptional_coefficient_mass {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Ioc N (2 * N),
      ‖(F n - mrtTypicalCoefficient J P F n) / (n : ℂ)‖ ^ 2) ≤
      (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N ^ 2 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    _ ≤ ∑ n ∈ Ioc N (2 * N), if ¬mrtTypical J P n then (1 / (N : ℝ)) ^ 2 else 0 := by
      apply sum_le_sum
      intro n hn
      have hn0 : 0 < n := hN.trans (mem_Ioc.mp hn).1
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1.le
      by_cases ht : mrtTypical J P n
      · simp [mrtTypicalCoefficient, ht]
      · simp only [mrtTypicalCoefficient, ht, ite_false, sub_zero, not_false_eq_true, ite_true]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        rw [norm_div, Complex.norm_natCast]
        exact (div_le_div_of_nonneg_right (hF n hn0) (by positivity)).trans
          (one_div_le_one_div_of_le hNr hnR)
    _ = _ := by rw [← sum_filter]; simp [div_eq_mul_inv]

/-- The error from excluding atypical integers costs their density, even
when the near-frequency interval grows. -/
theorem halasz_exceptional_dyadic_energy {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial F N t -
        mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      8 * Real.exp 1 * (T / N + 2) *
        (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm := mrt_dirichlet_mean_square_subset (Ioc N (2 * N))
    (N := 2 * N) (by
      intro n hn
      exact mem_Ioc.mpr ⟨lt_trans hN (mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2⟩)
    (fun n => (F n - mrtTypicalCoefficient J P F n) / (n : ℂ)) hT
  change (∫ t in -T..T, ‖mrtDyadicPolynomial
    (fun n => F n - mrtTypicalCoefficient J P F n) N t‖ ^ 2) ≤ _ at hm
  simp_rw [halasz_dyadic_sub] at hm
  apply hm.trans
  calc
    _ ≤ 8 * Real.exp 1 * (T + ((2 * N : ℕ) : ℝ)) *
        ((((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N ^ 2) :=
      mul_le_mul_of_nonneg_left (halasz_exceptional_coefficient_mass J P F hF hN) (by positivity)
    _ = _ := by push_cast; field_simp

end TwoPointCorrelations

end OAI
