import OAI.Analysis.CircleDomains.Selection.SquareVisitTolls

namespace OAI

/-! Two distinguished terminal hits and the remaining square tails control
the sum appearing in the independent dust-meeting bound. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

def awayFromTwo {A : Type*} (p q : A) (a : A → ℝ≥0∞) : A → ℝ≥0∞ :=
  fun x => if x = p ∨ x = q then 0 else a x

theorem two_terminal_hit_sum_bound {A : Type*} [Countable A]
    (a b : A → ℝ≥0∞) (p q : A) (ha : a p ≤ 1) (hb : b q ≤ 1) :
    (∑' x, a x * b x) ≤ b p + a q +
      countingSquareNorm (awayFromTwo p q a) * countingSquareNorm (awayFromTwo p q b) := by
  have hpoint (x : A) : a x * b x ≤
      (if x = p then b p else 0) + (if x = q then a q else 0) +
        awayFromTwo p q a x * awayFromTwo p q b x := by
    by_cases hxp : x = p
    · subst x
      have h : a p * b p ≤ b p := by simpa using mul_le_mul' ha (le_refl (b p))
      simpa only [awayFromTwo, true_or, ite_true, zero_mul, add_zero] using
        h.trans (le_add_right le_rfl)
    · by_cases hxq : x = q
      · subst x
        have h : a q * b q ≤ a q := by simpa using mul_le_mul' (le_refl (a q)) hb
        simpa [awayFromTwo, hxp] using h
      · simp [awayFromTwo, hxp, hxq]
  calc
    (∑' x, a x * b x) ≤ ∑' x, ((if x = p then b p else 0) + (if x = q then a q else 0) +
        awayFromTwo p q a x * awayFromTwo p q b x) := ENNReal.tsum_le_tsum hpoint
    _ = b p + a q + ∑' x, awayFromTwo p q a x * awayFromTwo p q b x := by
      rw [ENNReal.tsum_add, ENNReal.tsum_add]
      simp
    _ ≤ _ := add_le_add le_rfl (tsum_mul_le_countingSquareNorm _ _)

theorem two_terminal_hit_sum_le {A : Type*} [Countable A]
    (a b : A → ℝ≥0∞) (p q : A) (ha : a p ≤ 1) (hb : b q ≤ 1)
    {δ : ℝ≥0∞} (hab : b p ≤ δ) (hba : a q ≤ δ)
    (hatail : countingSquareNorm (awayFromTwo p q a) ≤ δ)
    (hbtail : countingSquareNorm (awayFromTwo p q b) ≤ δ) :
    (∑' x, a x * b x) ≤ 2 * δ + δ ^ 2 := by
  apply (two_terminal_hit_sum_bound a b p q ha hb).trans
  calc
    _ ≤ δ + δ + δ * δ := add_le_add (add_le_add hab hba) (mul_le_mul' hatail hbtail)
    _ = 2 * δ + δ ^ 2 := by rw [← two_mul, pow_two]

end CircleDomainRigidity

end

end OAI
