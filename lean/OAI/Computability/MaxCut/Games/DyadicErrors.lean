import Mathlib
import OAI.Computability.MaxCut.Games.GapSemantics

namespace OAI

/-! The final passage from positive dyadic error tolerances to arbitrary real
error tolerances, with exact finite numerator/denominator encodings. -/

namespace MaxCutGames.Integration.DyadicErrors

open MaxCutGames.Foundations.Target
open GapSemantics

/-- The index starts at denominator four, so every encoded error is below one half. -/
def dyadicError (n : Nat) : RationalError where
  numerator := 1
  denominator := 2 ^ (n + 2)
  numeratorPositive := by decide
  denominatorPositive := by positivity
  belowHalf := by
    have h : 2 ^ 2 ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at h ⊢
    omega

theorem errorValue_dyadic (n : Nat) :
    errorValue (dyadicError n) = (1 / 2 : ℚ) ^ (n + 2) := by
  simp [errorValue, dyadicError]

/-- Positive dyadic errors are cofinal among all positive real tolerances. -/
theorem exists_dyadic_below_real {ε : ℝ} (hε : 0 < ε) :
    ∃ n : Nat, (errorValue (dyadicError n) : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n, ?_⟩
  have hnat : n + 1 ≤ 2 ^ (n + 2) :=
    le_trans (Nat.succ_le_of_lt Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hden : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (n + 2) := by exact_mod_cast hnat
  have hfrac : (1 : ℝ) / 2 ^ (n + 2) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hden
  simpa [errorValue_dyadic, div_pow] using lt_of_le_of_lt hfrac hn

theorem exists_dyadic_below (e : RationalError) :
    ∃ n : Nat, errorValue (dyadicError n) < errorValue e := by
  have he : (0 : ℝ) < errorValue e := by exact_mod_cast errorValue_pos e
  obtain ⟨n, hn⟩ := exists_dyadic_below_real he
  exact ⟨n, by exact_mod_cast hn⟩

/-- A proved dyadic completeness gap gives the claimed real tolerance. -/
theorem completeAt_real_of_dyadic {q n : Nat} {ε : ℝ} {g : Instance q}
    (hε : (errorValue (dyadicError n) : ℝ) ≤ ε)
    (hg : CompleteAt (dyadicError n) g) :
    ∃ labeling, 1 - ε ≤
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length := by
  obtain ⟨labeling, hl⟩ := (completeAt_iff_real (dyadicError n) g).1 hg
  exact ⟨labeling, le_trans (sub_le_sub_left hε 1) hl⟩

theorem soundAt_real_of_dyadic {q n : Nat} {δ : ℝ} {g : Instance q}
    (hδ : (errorValue (dyadicError n) : ℝ) ≤ δ)
    (hg : SoundAt (dyadicError n) g) :
    ∀ labeling, (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ δ := by
  intro labeling
  exact le_trans ((soundAt_iff_real (dyadicError n) g).1 hg labeling) hδ

end MaxCutGames.Integration.DyadicErrors

end OAI
