import OAI.NumberTheory.Ostmann.Characters.CharacterFourthBound

namespace OAI

/-!
# Removing the principal character from the fourth moment

Its contribution cancels the leading fourth power of the total mass.
This leaves the second-moment term required by the two-bad quartet case.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance principalFourthFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance principalFourthDecidableEq {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

theorem weightedCharacterSum_principal {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (a : ZMod p) :
    weightedCharacterSum w 1 a = ((∑ b : ZMod p, w b) - w a : ℝ) := by
  classical
  have hterm (b : ZMod p) : (w b : ℂ) * (1 : MulChar (ZMod p) ℂ) (a - b) =
      (w b : ℂ) - if b = a then (w a : ℂ) else 0 := by
    by_cases hb : b = a
    · simp [hb, MulChar.map_zero]
    · have hab : a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
      rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hab)]
      simp only [hb, ite_false, sub_zero, mul_one]
  simp only [weightedCharacterSum, hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Complex.ofReal_sub, Complex.ofReal_sum]

private theorem fourth_tangent (J x : ℝ) : J ^ 4 - 4 * J ^ 3 * x ≤ (J - x) ^ 4 := by
  have h : 0 ≤ x ^ 2 * ((x - 2 * J) ^ 2 + 2 * J ^ 2) := by positivity
  nlinarith

theorem principal_fourth_moment_lower {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) :
    ((p : ℝ) - 4) * (∑ b : ZMod p, w b) ^ 4 ≤
      ∑ a : ZMod p, ‖weightedCharacterSum w 1 a‖ ^ 4 := by
  simp_rw [weightedCharacterSum_principal, Complex.norm_real, Real.norm_eq_abs,
    (show Even (4 : ℕ) by decide).pow_abs]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (a : ZMod p) _ => fourth_tangent (∑ b : ZMod p, w b) (w a))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, ← Finset.mul_sum] at h
  convert h using 1
  ring

/-- The leading `J⁴` cancels after removing the principal character. -/
theorem nonprincipal_fourth_moment_bound {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ χ ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
      ∑ a : ZMod p, ‖weightedCharacterSum w χ a‖ ^ 4) ≤
      2 * (p : ℝ) * (Fintype.card (ZMod p)ˣ : ℝ) *
        (∑ b : ZMod p, w b ^ 2) ^ 2 + 3 * (∑ b : ZMod p, w b) ^ 4 := by
  classical
  have hc : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  have htotal := (div_le_iff₀ hc).mp (weightedCharacterSum_fourth_bound w hw)
  have hprincipal := principal_fourth_moment_lower w
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (MulChar (ZMod p) ℂ))
    (fun χ => ∑ a : ZMod p, ‖weightedCharacterSum w χ a‖ ^ 4) (Finset.mem_univ 1)
  rw [hcard] at htotal ⊢
  nlinarith

end Ostmann

end OAI
