import Mathlib

namespace OAI

open scoped BigOperators
namespace Ostmann.HybridSieve

noncomputable def ordinateDerivativeCoefficients (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * (-Complex.I * (Real.log n : ℂ))

theorem finite_ordinate_sum_hasDerivAt (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => ∑ n ∈ s, a n * Complex.exp (-Complex.I * (u : ℂ) * (Real.log n : ℂ)))
      (∑ n ∈ s, ordinateDerivativeCoefficients a n *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ))) t := by
  apply HasDerivAt.fun_sum
  intro n hn
  have h := ((((hasDerivAt_id (t : ℂ)).const_mul (-Complex.I)).mul_const
    (Real.log n : ℂ)).cexp).comp_ofReal
  convert h.const_mul (a n) using 1 <;> dsimp [ordinateDerivativeCoefficients]
  ring

theorem finite_ordinate_sum_continuous (s : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (fun t : ℝ => ∑ n ∈ s,
      a n * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ))) :=
  continuous_iff_continuousAt.mpr fun t => (finite_ordinate_sum_hasDerivAt s a t).continuousAt

theorem norm_ordinateDerivativeCoefficients (a : ℕ → ℂ) (n : ℕ) :
    ‖ordinateDerivativeCoefficients a n‖ = ‖a n‖ * |Real.log n| := by
  simp only [ordinateDerivativeCoefficients, norm_mul, norm_neg, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem ordinateDerivativeCoefficients_energy (N : ℕ) (a : ℕ → ℂ) (_hN : 0 < N) :
    (∑ n ∈ Finset.Ioc N (2 * N), ‖ordinateDerivativeCoefficients a n‖ ^ 2) ≤
      (Real.log (2 * N : ℝ)) ^ 2 * ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨hn₁, hn₂⟩ := Finset.mem_Ioc.mp hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnm : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn₂
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hlogM : Real.log n ≤ Real.log (2 * N : ℝ) :=
    Real.log_le_log (by linarith) hnm
  rw [norm_ordinateDerivativeCoefficients, abs_of_nonneg hlog, mul_pow, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  nlinarith

end Ostmann.HybridSieve

end OAI
