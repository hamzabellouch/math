import OAI.NumberTheory.SiegelZeros.EntireFunctions.NormalizedHadamardTransfer
import OAI.NumberTheory.SiegelZeros.Estimates.ConstantCancellation

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace WeightedTorusJets.W63

theorem normalizedZeroSumAt_of_actual_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprimitive : χ.IsPrimitive) (hnp : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) {s : ℝ} (hs : 1 < s) :
    NormalizedZeroSumAt χ s := by
  obtain ⟨A, B, haffine⟩ :=
    SiegelZerosAwei.Workers.W01.normalizedCompletion_affine_factorization
      χ hnp hprimitive
  have hne : SiegelZerosAwei.W51.normalizedCompletion χ (s : ℂ) ≠ 0 :=
    SiegelZerosAwei.W51.normalizedCompletion_ne_zero_of_one_le_re χ hnp
      (by simpa using hs.le)
  refine ⟨(SiegelZerosAwei.W51.actual_zero_sum_convergence χ hnp hprimitive hne).2.2, ?_⟩
  exact SiegelZerosAwei.W51.real_logDeriv_normalizedCompletion_eq_zero_sum_of_affine
    χ hnp hprimitive hreal A B haffine hne

theorem hadamardFormulaAt_of_actual_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprimitive : χ.IsPrimitive) (hnp : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) {s : ℝ} (hs : 1 < s) :
    HadamardFormulaAt χ s :=
  (normalizedZeroSumAt_of_actual_character χ hprimitive hnp hreal hs).to_HadamardFormulaAt hnp hs

theorem exists_prime_bias_for_actual_zeros :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β X : ℝ,
      0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 → 3 ≤ X →
      SiegelZeros.W07.primeMass
        (SiegelZeros.W07.valuePrimes χ (SiegelZeros.W08.primesUpTo X) 1) ≤
      C * Real.log q + C * (1 - β) * Real.log X ^ 2 := by
  obtain ⟨C, hC, hbias⟩ := exists_prime_bias_for_actual_zeros_of_HadamardFormula
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX
  exact hbias q hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX
    (hadamardFormulaAt_of_actual_character χ hprimitive hnp hreal
      (W04.logarithmic_parameter_range X hX).1)

theorem exists_good_mass_for_actual_zeros :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ, 0 ≤ CH ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β X : ℝ,
      0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 → 3 ≤ X →
      Real.log X - C * Real.log q -
        C * (((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q) - CH ≤
      SiegelZeros.W07.primeMass
        (SiegelZeros.W07.goodPrimes χ (SiegelZeros.W08.primesUpTo X) H) := by
  obtain ⟨C, hC, hmass⟩ := exists_good_mass_for_actual_zeros_of_HadamardFormula
  refine ⟨C, hC, ?_⟩
  intro H hH
  obtain ⟨CH, hCH⟩ := hmass H hH
  refine ⟨max CH 0, le_max_right _ _, ?_⟩
  intro q _ hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX
  have h := hCH q hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX
    (hadamardFormulaAt_of_actual_character χ hprimitive hnp hreal
      (W04.logarithmic_parameter_range X hX).1)
  exact (sub_le_sub_left (le_max_left CH 0) _).trans h

theorem exists_good_mass_for_actual_zeros_normalized :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧
      ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ, 0 ≤ CH ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β X : ℝ,
      0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 → 3 ≤ X →
      Real.log X - C * Real.log q -
        C * (((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q) - CH ≤
      SiegelZeros.W07.primeMass
        (SiegelZeros.W07.goodPrimes χ (SiegelZeros.W08.primesUpTo X) H) := by
  obtain ⟨C, hC, hmass⟩ := exists_good_mass_for_actual_zeros
  refine ⟨max C (Real.log 4), lt_of_lt_of_le hC (le_max_left _ _),
    le_max_right _ _, ?_⟩
  intro H hH
  obtain ⟨CH, hCH, hbound⟩ := hmass H hH
  refine ⟨CH, hCH, ?_⟩
  intro q _ hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX
  have h := hbound q hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 ≤ Real.log (q : ℝ) := (Real.log_pos hq1).le
  have herr : 0 ≤ ((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q := by
    rw [← W04.delta_substitution (q : ℝ) X β hq1]
    exact mul_nonneg (sub_nonneg.mpr hβ1.le) (sq_nonneg _)
  have hconductor := mul_le_mul_of_nonneg_right (le_max_left C (Real.log 4)) hlogq
  have herror := mul_le_mul_of_nonneg_right (le_max_left C (Real.log 4)) herr
  linarith

end WeightedTorusJets.W63

end

end

end SiegelZeros

end OAI
