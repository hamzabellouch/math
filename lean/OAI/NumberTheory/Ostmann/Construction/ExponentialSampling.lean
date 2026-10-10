import Mathlib.Analysis.SpecificLimits.Basic
import OAI.NumberTheory.Ostmann.Preliminaries.SummandLogarithmicLower

namespace OAI

/-! # Exponential cutoffs for the two-length summand comparison -/

namespace Ostmann

open Filter

noncomputable def exponentialSample (t : ℕ) : ℕ := ⌈Real.exp (t : ℝ)⌉₊

 theorem exponentialSample_tendsto : Tendsto exponentialSample atTop atTop :=
  tendsto_nat_ceil_atTop.comp (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop)

 theorem exponentialSample_log (t : ℕ) :
    (t : ℝ) ≤ Real.log (exponentialSample t : ℝ) ∧
      Real.log (exponentialSample t : ℝ) ≤ t + 1 := by
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
  have he : 1 ≤ Real.exp (t : ℝ) := Real.one_le_exp ht
  have hlo : Real.exp (t : ℝ) ≤ (exponentialSample t : ℝ) := Nat.le_ceil _
  have hhi : (exponentialSample t : ℝ) ≤ 2 * Real.exp (t : ℝ) := by
    have hh := (Nat.ceil_lt_add_one (Real.exp_pos (t : ℝ)).le).le
    change (exponentialSample t : ℝ) ≤ _ at hh
    linarith
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hlo
  · have hh := Real.log_le_log ((Real.exp_pos _).trans_le hlo) hhi
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith

 theorem EventuallyPrimeSumset.exponential_sample_population {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Infinite) :
    ∀ᶠ t : ℕ in atTop,
      1 ≤ exponentialSample t ∧ (summandPrefix B (exponentialSample t)).Nonempty ∧
      3 * (t : ℝ) ^ 6 ≤ ((summandPrefix B (exponentialSample t)).card : ℝ) := by
  obtain ⟨c, hc, hpop⟩ := h.symm.summand_logarithmic_lower hB 12
  have hlarge := ((tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (3 / c))
  filter_upwards [exponentialSample_tendsto.eventually hpop, hlarge,
    eventually_ge_atTop (1 : ℕ)] with t hp ht ht1
  have htp : 0 < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hlog := (exponentialSample_log t).1
  have hpow : (t : ℝ) ^ 12 ≤ Real.log (exponentialSample t : ℝ) ^ 12 := by gcongr
  change 3 / c ≤ (t : ℝ) ^ 6 at ht
  have hmult : 3 ≤ c * (t : ℝ) ^ 6 := by
    have hh := (div_le_iff₀ hc).mp ht
    nlinarith
  have hcount : 3 * (t : ℝ) ^ 6 ≤ ((summandPrefix B (exponentialSample t)).card : ℝ) := by
    calc
      _ ≤ c * (t : ℝ) ^ 12 := by nlinarith [mul_le_mul_of_nonneg_right hmult (pow_nonneg htp.le 6)]
      _ ≤ c * Real.log (exponentialSample t : ℝ) ^ 12 := mul_le_mul_of_nonneg_left hpow hc.le
      _ ≤ _ := hp
  have hne : (summandPrefix B (exponentialSample t)).Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < (summandPrefix B (exponentialSample t)).card :=
      (by positivity : 0 < 3 * (t : ℝ) ^ 6).trans_le hcount
    exact_mod_cast hh
  have hsample : 1 ≤ exponentialSample t := by
    have hh : (0 : ℝ) < (exponentialSample t : ℝ) :=
      (Real.exp_pos _).trans_le (Nat.le_ceil _)
    have hh' : 0 < exponentialSample t := by exact_mod_cast hh
    omega
  exact ⟨hsample, hne, hcount⟩

end Ostmann

end OAI
