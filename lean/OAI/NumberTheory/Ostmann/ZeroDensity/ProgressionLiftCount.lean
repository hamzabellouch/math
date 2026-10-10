import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! # Uniform integer-lift counts in a residue class -/

namespace Ostmann

/-- A residue class has at most interval length / modulus + 1 representatives.
This form is uniform in the residue and works across zero. -/
theorem progression_Ico_card_le (lo hi q r : ℤ) (hlo : lo ≤ hi) (hq : 0 < q) :
    (((Finset.Ico lo hi).filter fun n => n ≡ r [ZMOD q]).card : ℚ) ≤
      ((hi : ℚ) - lo) / q + 1 := by
  let A : ℚ := ((lo : ℚ) - r) / q
  let B : ℚ := ((hi : ℚ) - r) / q
  have hcard := Int.Ico_filter_modEq_card lo hi hq r
  have hcast : (((Finset.Ico lo hi).filter fun n => n ≡ r [ZMOD q]).card : ℚ) =
      max (((⌈B⌉ : ℤ) : ℚ) - ((⌈A⌉ : ℤ) : ℚ)) 0 := by
    dsimp [A, B]
    exact_mod_cast hcard
  have ha : A ≤ (⌈A⌉ : ℤ) := Int.le_ceil A
  have hb : ((⌈B⌉ : ℤ) : ℚ) < B + 1 := Int.ceil_lt_add_one B
  have hdiff : ((⌈B⌉ : ℤ) : ℚ) - ((⌈A⌉ : ℤ) : ℚ) ≤
      ((hi : ℚ) - lo) / q + 1 := by
    calc
      _ ≤ B - A + 1 := by linarith
      _ = _ := by dsimp [A, B]; ring
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hwidth : (0 : ℚ) ≤ (hi : ℚ) - lo := by exact_mod_cast sub_nonneg.mpr hlo
  rw [hcast]
  exact max_le hdiff (by positivity)

end Ostmann

end OAI
