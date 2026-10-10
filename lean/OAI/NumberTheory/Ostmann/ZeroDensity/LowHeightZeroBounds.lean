import OAI.NumberTheory.Ostmann.ZeroDensity.ShiftedRealHadamard
import OAI.NumberTheory.Ostmann.ZeroDensity.LowHeightArchimedean
import OAI.NumberTheory.Ostmann.ZeroDensity.DirichletLogDerivativeBound

namespace OAI

/-! # Actual zero sums and bounded low-height errors -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem shifted_real_zero_sum_nonneg (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) : 0 ≤ shiftedRealCharacterZeroSum χ s := by
  apply tsum_nonneg
  intro i
  rw [realZeroKernel_complex_sub]
  exact realZeroKernel_nonneg (by linarith [((realCharacterActualZeros χ).in_strip i).2])

theorem shifted_real_zero_term_le (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) (i : ℕ) :
    ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re ≤ shiftedRealCharacterZeroSum χ s := by
  exact (shifted_real_zero_summable χ s hs hs2).le_tsum i (fun j _ => by
    rw [realZeroKernel_complex_sub]
    exact realZeroKernel_nonneg (by linarith [((realCharacterActualZeros χ).in_strip j).2]))

theorem shifted_real_zero_pair_le (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) (i j : ℕ) (hij : i ≠ j) :
    ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re +
      ((s - (realCharacterActualZeros χ).zeros j)⁻¹).re ≤ shiftedRealCharacterZeroSum χ s := by
  have hh := (shifted_real_zero_summable χ s hs hs2).sum_le_tsum {i,j} (fun k _ => by
    rw [realZeroKernel_complex_sub]
    exact realZeroKernel_nonneg (by linarith [((realCharacterActualZeros χ).in_strip k).2]))
  simpa only [Finset.sum_pair hij, shiftedRealCharacterZeroSum] using hh

/-- Uniform upper error after replacing the completed logarithmic derivative
by the ordinary one in the actual shifted zero identity. -/
theorem exists_low_height_zero_sum_error : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveRealCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 → |s.im| ≤ 2 →
      shiftedRealCharacterZeroSum χ s ≤ (logDeriv χ.L s).re +
        (1 / 2) * Real.log χ.modulus + C := by
  obtain ⟨C, hC, hb⟩ := characterGamma_low_height_bound
  refine ⟨C, hC, ?_⟩
  intro χ s hs hs2 hi
  rw [shifted_real_hadamard_identity χ s hs hs2,
    χ.asComplex.completed_logDeriv_eq_add s hs.le, PrimitiveRealCharacter.asComplex_L,
    Complex.add_re]
  have hh := (Complex.re_le_norm _).trans (hb χ.asComplex s hs hs2 hi)
  linarith

/-- On the real axis the elementary Euler bound gives a single pole, uniformly
in the primitive real character. -/
theorem exists_real_zero_sum_upper : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveRealCharacter) (s : ℝ), 1 < s → s ≤ 2 →
      shiftedRealCharacterZeroSum χ (s : ℂ) ≤ 1 / (s - 1) +
        (1 / 2) * Real.log χ.modulus + C := by
  obtain ⟨C, hC, hb⟩ := exists_low_height_zero_sum_error
  obtain ⟨D, hD, hd⟩ := exists_dirichlet_logDerivative_bound
  refine ⟨C + D, by positivity, ?_⟩
  intro χ s hs hs2
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hh := hb χ (s : ℂ) hs hs2 (by simp)
  have hnorm := hd χ.modulus χ.complexCharacter s hs hs2
  change ‖logDeriv χ.L (s : ℂ)‖ ≤ _ at hnorm
  have hre := (Complex.re_le_norm _).trans hnorm
  linarith

theorem exists_low_height_vonMangoldt_upper : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 2 →
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤
        realZeroKernel (s.re - 1) s.im + C := by
  obtain ⟨C, hC, hb⟩ := vonMangoldt_low_height_pole_error
  refine ⟨C, hC, ?_⟩
  intro s hs hs2 hi
  have hh := (Complex.re_le_norm _).trans (hb s hs hs2 hi)
  rw [Complex.sub_re] at hh
  have he : ((s - 1)⁻¹).re = realZeroKernel (s.re - 1) s.im := by
    simpa using realZeroKernel_complex_sub s 1
  rw [he] at hh
  linarith

end Ostmann

end OAI
