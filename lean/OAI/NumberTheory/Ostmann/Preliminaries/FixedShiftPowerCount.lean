import OAI.NumberTheory.Ostmann.Preliminaries.FixedShiftSieveBound
import OAI.NumberTheory.Ostmann.Preliminaries.FixedShiftMertensWeights

namespace OAI

/-! # Fixed-shift counting at integer-power sieve cutoffs -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem fixed_shift_power_count (B : Finset ℕ) (hB : B.Nonempty) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop, ∀ M : ℕ, 1 ≤ M →
      ∀ A : Finset (Fin M), A.Nonempty →
      (∀ a ∈ A, R ^ (10 * B.card) < a.val) →
      (∀ a ∈ A, ∀ b ∈ B, (a.val + b).Prime) →
      (A.card : ℝ) * Real.log (R : ℝ) ^ B.card ≤
        C * ((M : ℝ) + ((R ^ (10 * B.card) : ℕ) : ℝ) ^ 2) := by
  let p₀ := max (B.sup id) B.card
  have hj : 1 ≤ B.card := hB.card_pos
  have hjp : B.card ≤ p₀ := le_max_right _ _
  obtain ⟨c, hc, hweights⟩ := fixed_shift_weight_at_power p₀ B.card hj hjp
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  filter_upwards [hweights, eventually_ge_atTop (2 : ℕ)] with R hR hR2
  intro M hM A hA hlarge hprime
  have hRQ : R ≤ R ^ (10 * B.card) := Nat.le_self_pow (by omega) R
  have hQ : 1 ≤ R ^ (10 * B.card) := (by omega : 1 ≤ R).trans hRQ
  have hP : ∀ p ∈ fixedShiftPrimeSet p₀ R, p.Prime :=
    fun p hp => (mem_fixedShiftPrimeSet.mp hp).1
  have hPQ : ∀ p ∈ fixedShiftPrimeSet p₀ R, p ≤ R ^ (10 * B.card) :=
    fun p hp => (mem_fixedShiftPrimeSet.mp hp).2.2.trans hRQ
  have hb : ∀ p ∈ fixedShiftPrimeSet p₀ R, ∀ b ∈ B, b < p := by
    intro p hp b hb
    have hb0 : b ≤ p₀ := (Finset.le_sup (f := id) hb).trans (le_max_left _ _)
    exact hb0.trans_lt (mem_fixedShiftPrimeSet.mp hp).2.1
  have hbc : ∀ p ∈ fixedShiftPrimeSet p₀ R, B.card < p :=
    fun p hp => hjp.trans_lt (mem_fixedShiftPrimeSet.mp hp).2.1
  have hsieve := fixed_shift_sieve_bound B (fixedShiftPrimeSet p₀ R) hM hQ A hA
    hP hPQ hb hbc hlarge hprime
  have hbound := hR.trans hsieve
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hmul := (le_div_iff₀ hAc).mp hbound
  rw [mul_comm c⁻¹ _, ← div_eq_mul_inv]
  apply (le_div_iff₀ hc).mpr
  nlinarith

end Ostmann

end OAI
