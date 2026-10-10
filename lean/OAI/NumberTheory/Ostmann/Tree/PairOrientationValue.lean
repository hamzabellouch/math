import OAI.NumberTheory.Ostmann.Tree.RationalPairValue

namespace OAI

/-! # Reversing the free and held leaves of a bottom pair -/

namespace Ostmann

open scoped ComplexConjugate

theorem fieldBottomPairValue_formula {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) (hd : d ≠ 0) (ht : t ≠ 0) :
    fieldBottomPairValue g d t = if t = 1 then 0 else
      g (d * t / (t - 1)) * conj (g (d / (t - 1))) := by
  have hi : (Units.mk0 t ht : (ZMod p)ˣ) = 1 ↔ t = 1 := by
    constructor
    · exact fun h => congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    · exact fun h => Units.ext h
  simp only [fieldBottomPairValue, hd, ht, dite_false, bottomPairValue, hi, Units.val_mk0]

/-- Reversing a pair negates its difference, inverts its ratio and conjugates
its base function. The two leaf factors themselves remain unchanged. -/
theorem fieldBottomPairValue_reverse {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) :
    fieldBottomPairValue (fun x => conj (g x)) (-d) t⁻¹ = fieldBottomPairValue g d t := by
  by_cases hd : d = 0
  · simp [hd]
  by_cases ht : t = 0
  · simp [ht]
  rw [fieldBottomPairValue_formula _ _ _ (neg_ne_zero.mpr hd) (inv_ne_zero ht),
    fieldBottomPairValue_formula g d t hd ht]
  by_cases ht1 : t = 1
  · simp [ht1]
  have hi1 : t⁻¹ ≠ 1 := by
    intro h
    apply ht1
    simpa only [inv_inv, inv_one] using congrArg (fun x : ZMod p => x⁻¹) h
  simp only [ht1, hi1, ite_false, starRingEnd_apply, star_star]
  have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have ha : -d * t⁻¹ / (t⁻¹ - 1) = d / (t - 1) := by field_simp; ring
  have hb : -d / (t⁻¹ - 1) = d * t / (t - 1) := by field_simp; ring
  rw [ha, hb]
  exact mul_comm _ _

theorem fieldBottomPairValue_negate {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) :
    fieldBottomPairValue (fun x => g (-x)) d t = fieldBottomPairValue g (-d) t := by
  by_cases hd : d = 0
  · simp [hd]
  by_cases ht : t = 0
  · simp [ht]
  rw [fieldBottomPairValue_formula _ _ _ hd ht,
    fieldBottomPairValue_formula _ _ _ (neg_ne_zero.mpr hd) ht]
  split_ifs
  · rfl
  · simp only [neg_mul, neg_div]

/-- Reversing the pair while keeping its difference positive reflects and
conjugates the base function. -/
theorem fieldBottomPairValue_reflect_reverse {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) :
    fieldBottomPairValue (fun x => conj (g (-x))) d t⁻¹ = fieldBottomPairValue g d t := by
  rw [fieldBottomPairValue_negate (fun x => conj (g x)), fieldBottomPairValue_reverse]

end Ostmann

end OAI
