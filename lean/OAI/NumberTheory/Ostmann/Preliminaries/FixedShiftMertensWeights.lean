import OAI.NumberTheory.Ostmann.Preliminaries.FixedShiftEulerLower
import OAI.NumberTheory.Ostmann.Preliminaries.BoundedSieveSubsets
import OAI.NumberTheory.Ostmann.MainWithoutProgression
import OAI.NumberTheory.Ostmann.ZeroDensity.MertensFromProgression

namespace OAI

/-! # Mertens bounds for the actual fixed-shift Euler weights -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

noncomputable def fixedShiftPrimeSet (p₀ R : ℕ) : Finset ℕ :=
  Nat.primesLE R \ Nat.primesLE p₀

 theorem mem_fixedShiftPrimeSet {p₀ R p : ℕ} :
    p ∈ fixedShiftPrimeSet p₀ R ↔ p.Prime ∧ p₀ < p ∧ p ≤ R := by
  simp only [fixedShiftPrimeSet, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpR, hp⟩, hnot⟩
    have hn : ¬ p ≤ p₀ := fun hh => hnot ⟨hh, hp⟩
    exact ⟨hp, by omega, hpR⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨hhi, hp⟩, by omega⟩

 theorem fixedShiftPrimeSet_harmonic_lower (p₀ : ℕ) :
    ∃ C : ℝ, ∀ R : ℕ, max 2 p₀ ≤ R →
      Real.log (Real.log (R : ℝ)) - C ≤
        ∑ p ∈ fixedShiftPrimeSet p₀ R, 1 / (p : ℝ) := by
  let D := |1 - Real.log (Real.log 2)| +
    (2 * actualProgressionInput.mertensConstant + Real.log 2) / Real.log 2
  have hH : MertensHarmonicEstimate D := actualProgressionInput.mertens.harmonic
  refine ⟨D + ∑ p ∈ Nat.primesLE p₀, 1 / (p : ℝ), ?_⟩
  intro R hR
  have hR2 : 2 ≤ R := (le_max_left _ _).trans hR
  have hpR : p₀ ≤ R := (le_max_right _ _).trans hR
  have hsub : Nat.primesLE p₀ ⊆ Nat.primesLE R := by
    intro p hp
    obtain ⟨hpp, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpp.trans hpR, hpprime⟩
  have hs := Finset.sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) hsub
  have hb := (abs_le.mp (hH R hR2)).1
  simp only [← one_div] at hb
  change (∑ p ∈ fixedShiftPrimeSet p₀ R, 1 / (p : ℝ)) +
    (∑ p ∈ Nat.primesLE p₀, 1 / (p : ℝ)) = _ at hs
  linarith

 theorem fixedShiftPrimeSet_log_upper (p₀ R : ℕ) (hR : 1 ≤ R) :
    (∑ p ∈ fixedShiftPrimeSet p₀ R, Real.log (p : ℝ) / p) ≤
      Real.log (R : ℝ) + actualProgressionInput.mertensConstant := by
  apply le_trans _ (actualProgressionInput.mertens.upper R hR)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
  intro p hp _
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
    (Nat.cast_nonneg p)

 theorem fixed_shift_euler_power_lower (p₀ j : ℕ) (hj : j ≤ p₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℕ, max 2 p₀ ≤ R →
      c * Real.log (R : ℝ) ^ j ≤
        ∏ p ∈ fixedShiftPrimeSet p₀ R, (p : ℝ) / ((p : ℝ) - j) := by
  obtain ⟨C, hC⟩ := fixedShiftPrimeSet_harmonic_lower p₀
  refine ⟨Real.exp (-(j : ℝ) * C), Real.exp_pos _, ?_⟩
  intro R hR
  apply fixed_shift_euler_log_lower _ j R C
  · exact_mod_cast (show 1 < R from lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hR))
  · intro p hp
    exact_mod_cast lt_of_le_of_lt hj (mem_fixedShiftPrimeSet.mp hp).2.1
  · exact hC R hR

 theorem fixed_shift_weight_at_power (p₀ j : ℕ) (hj : 1 ≤ j) (hjp : j ≤ p₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ R : ℕ in atTop,
      c * Real.log (R : ℝ) ^ j ≤
        ∑ U ∈ boundedSieveSubsets (fixedShiftPrimeSet p₀ R) (R ^ (10 * j)),
          ∏ p ∈ U, (j : ℝ) / ((p : ℝ) - j) := by
  obtain ⟨c, hc, hweight⟩ := fixed_shift_euler_power_lower p₀ j hjp
  refine ⟨c / 2, by positivity, ?_⟩
  have hlog : ∀ᶠ R : ℕ in atTop, actualProgressionInput.mertensConstant ≤ Real.log (R : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hlog, eventually_ge_atTop (max 2 p₀)] with R hlog hR
  have hR2 : 2 ≤ R := (le_max_left _ _).trans hR
  have hR1 : 1 ≤ R := by omega
  have hprod : ∀ p ∈ fixedShiftPrimeSet p₀ R, (j : ℝ) < p := by
    intro p hp
    exact_mod_cast lt_of_le_of_lt hjp (mem_fixedShiftPrimeSet.mp hp).2.1
  have hQ : 2 ≤ R ^ (10 * j) := by
    have he : 1 ≤ 10 * j := by omega
    exact hR2.trans (Nat.le_self_pow (by omega : 10 * j ≠ 0) R)
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR1)
  have hlogQ : Real.log (R ^ (10 * j) : ℕ) = (10 * (j : ℝ)) * Real.log R := by
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  have hmean : (j : ℝ) * (∑ p ∈ fixedShiftPrimeSet p₀ R, Real.log (p : ℝ) / p) ≤
      Real.log (R ^ (10 * j) : ℕ) / 2 := by
    have hu := mul_le_mul_of_nonneg_left (fixedShiftPrimeSet_log_upper p₀ R hR1)
      (Nat.cast_nonneg (α := ℝ) j)
    rw [hlogQ]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hlogR]
  have hb := fixed_shift_bounded_weight (fixedShiftPrimeSet p₀ R) j (R ^ (10 * j))
    (Nat.cast_nonneg j) hQ hprod hmean
  have hcR := hweight R hR
  nlinarith

end Ostmann

end OAI
