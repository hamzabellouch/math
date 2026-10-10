import OAI.NumberTheory.SiegelZeros.Characters.MangoldtMass
import OAI.NumberTheory.SiegelZeros.Characters.PrimePowerTail
import OAI.NumberTheory.SiegelZeros.EntireFunctions.AvoidZeroRadii

namespace OAI

namespace SiegelZeros

section

namespace W55

open scoped BigOperators

theorem prime_mass_nat_lower {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) - (1 + higherPrimePowerConstant) ≤
      ∑ p ∈ (Finset.Ioc 0 n).filter Nat.Prime, Real.log p / (p : ℝ) := by
  have h := prime_mass_lower_of_vonMangoldt_mass_lower (Finset.Ioc 0 n)
    (Real.log (n : ℝ) - 1) (Result.W54.sum_vonMangoldt_div_lower hn)
  linarith

lemma log_floor_lower {X : ℝ} (hX : 1 ≤ X) :
    Real.log X - Real.log 2 ≤ Real.log (⌊X⌋₊ : ℝ) := by
  have hn : 1 ≤ ⌊X⌋₊ := Nat.floor_pos.mpr hX
  have hnR : (1 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hn
  have hxpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hfloorpos : (0 : ℝ) < (⌊X⌋₊ : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hxlt := Nat.lt_floor_add_one X
  have hdouble : X ≤ 2 * (⌊X⌋₊ : ℝ) := by linarith
  have hlog := Real.log_le_log hxpos hdouble
  rw [Real.log_mul (by norm_num) (ne_of_gt hfloorpos)] at hlog
  linarith

theorem prime_mass_real_lower {X : ℝ} (hX : 1 ≤ X) :
    Real.log X - (1 + higherPrimePowerConstant + Real.log 2) ≤
      ∑ p ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime, Real.log p / (p : ℝ) := by
  have hnat := prime_mass_nat_lower (Nat.floor_pos.mpr hX)
  have hlog := log_floor_lower hX
  linarith

theorem exists_absolute_prime_mass_lower :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      Real.log X - C ≤
        ∑ p ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime, Real.log p / (p : ℝ) := by
  refine ⟨1 + higherPrimePowerConstant + Real.log 2, ?_, fun X hX => prime_mass_real_lower hX⟩
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have htail := higherPrimePowerConstant_nonneg
  linarith

end W55

end

noncomputable section
namespace WeightedTorusJets.W63

theorem exists_good_prime_mass_of_hadamard :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β X : ℝ, β ≤ 1 → 3 ≤ X →
      HadamardExpansionAt χ β (1 + 1 / Real.log X) →
      Real.log X - C * Real.log q -
        C * (((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q) - CH ≤
      SiegelZeros.W07.primeMass
        (SiegelZeros.W07.goodPrimes χ (SiegelZeros.W08.primesUpTo X) H) := by
  obtain ⟨C, hC, hbias⟩ := exists_prime_bias_of_hadamard
  obtain ⟨Bm, hBm, hmertens⟩ := SiegelZeros.W55.exists_absolute_prime_mass_lower
  refine ⟨C + 1, by linarith, ?_⟩
  intro H hH
  refine ⟨Bm + SiegelZeros.W07.smallPrimeMass H, ?_⟩
  intro q _ hq χ hnp hreal β X hβ hX hhad
  have hqpos : 0 < q := by omega
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hb := hbias q hq χ hnp hreal β X hβ hX hhad
  have hdelta := W04.delta_substitution (q : ℝ) X β hq1
  have hS : ∀ p ∈ SiegelZeros.W08.primesUpTo X, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hm : Real.log X - Bm ≤
      SiegelZeros.W07.primeMass (SiegelZeros.W08.primesUpTo X) :=
    hmertens X (by linarith)
  have hb' : SiegelZeros.W07.primeMass
      (SiegelZeros.W07.valuePrimes χ (SiegelZeros.W08.primesUpTo X) 1) ≤
      C * Real.log q + C * ((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q := by
    calc
      _ ≤ C * Real.log q + C * ((1 - β) * Real.log X ^ 2) := by nlinarith [hb]
      _ = _ := by rw [hdelta]; ring
  have hg := SiegelZeros.W07.good_mass_from_primebias_mertens χ
    (SiegelZeros.W07.quadratic_of_real χ hreal) hqpos
    (SiegelZeros.W08.primesUpTo X) hS hH (Real.log X)
    ((1 - β) * Real.log q) C Bm hm hb'
  have herr : 0 ≤ ((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q := by
    rw [← hdelta]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hcoefficient : C * ((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q =
      C * (((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q) := by ring
  rw [hcoefficient] at hg
  have hweaken := mul_le_mul_of_nonneg_right (show C ≤ C + 1 by linarith) herr
  exact (sub_le_sub_right (sub_le_sub_left hweaken _) _).trans hg

theorem exists_good_prime_mass_for_target_zeros_of_hadamard :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β X : ℝ,
      0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 → 3 ≤ X →
      HadamardExpansionAt χ β (1 + 1 / Real.log X) →
      Real.log X - C * Real.log q -
        C * (((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q) - CH ≤
      SiegelZeros.W07.primeMass
        (SiegelZeros.W07.goodPrimes χ (SiegelZeros.W08.primesUpTo X) H) := by
  obtain ⟨C, hC, hmass⟩ := exists_good_prime_mass_of_hadamard
  refine ⟨C, hC, ?_⟩
  intro H hH
  obtain ⟨CH, hCH⟩ := hmass H hH
  refine ⟨CH, ?_⟩
  intro q _ hq χ _ hnp hreal β X _ hβ _ hX hhad
  exact hCH q hq χ hnp hreal β X hβ.le hX hhad

end WeightedTorusJets.W63

end

noncomputable section
namespace WeightedTorusJets.W63

theorem exists_prime_bias_for_actual_zeros_of_HadamardFormula :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β X : ℝ,
      0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 → 3 ≤ X →
      HadamardFormulaAt χ (1 + 1 / Real.log X) →
      SiegelZeros.W07.primeMass
        (SiegelZeros.W07.valuePrimes χ (SiegelZeros.W08.primesUpTo X) 1) ≤
      C * Real.log q + C * (1 - β) * Real.log X ^ 2 := by
  obtain ⟨C, hC, hbias⟩ := exists_prime_bias_of_hadamard
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX hformula
  exact hbias q hq χ hnp hreal β X hβ1.le hX
    (hformula.to_expansion hnp hprimitive hβ0 hzero)

theorem exists_good_mass_for_actual_zeros_of_HadamardFormula :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β X : ℝ,
      0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 → 3 ≤ X →
      HadamardFormulaAt χ (1 + 1 / Real.log X) →
      Real.log X - C * Real.log q -
        C * (((1 - β) * Real.log q) * Real.log X ^ 2 / Real.log q) - CH ≤
      SiegelZeros.W07.primeMass
        (SiegelZeros.W07.goodPrimes χ (SiegelZeros.W08.primesUpTo X) H) := by
  obtain ⟨C, hC, hmass⟩ := exists_good_prime_mass_for_target_zeros_of_hadamard
  refine ⟨C, hC, ?_⟩
  intro H hH
  obtain ⟨CH, hCH⟩ := hmass H hH
  refine ⟨CH, ?_⟩
  intro q _ hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX hformula
  exact hCH q hq χ hprimitive hnp hreal β X hβ0 hβ1 hzero hX
    (hformula.to_expansion hnp hprimitive hβ0 hzero)

end WeightedTorusJets.W63

end

end SiegelZeros

end OAI
