import OAI.Analysis.CircleDomains.Selection.TwoTerminalHitBound
import OAI.Analysis.CircleDomains.Probability.CountableLawRestriction

namespace OAI

/-! The two terminal contributions are controlled by the opposite punctured
square norm. No separate small individual-hit hypothesis is needed. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem countingSquareNorm_point_le {S : Type*} (m : S → ℝ≥0∞) (x : S) :
    m x ≤ countingSquareNorm m := by
  have h := countingSquareNorm_comp_injective m (fun _ : Unit => x)
    (fun _ _ _ => Subsingleton.elim _ _)
  simpa [countingSquareNorm, Function.comp_def, tsum_fintype,
    ← ENNReal.rpow_natCast_mul] using h

def puncturedHit {S : Type*} (m : S → ℝ≥0∞) (U : Set S) (p : S) : S → ℝ≥0∞ :=
  fun s => if s ∈ U ∧ s ≠ p then m s else 0

theorem punctured_hit_product_sum_le {S : Type*} [Countable S]
    (a b : S → ℝ≥0∞) (U : Set S) (p q : S) (hp : p ∈ U) (hq : q ∈ U)
    (hpq : p ≠ q) (ha : a p ≤ 1) (hb : b q ≤ 1) {δ : ℝ≥0∞}
    (hatail : countingSquareNorm (puncturedHit a U p) ≤ δ)
    (hbtail : countingSquareNorm (puncturedHit b U q) ≤ δ) :
    (∑' x, (if x ∈ U then a x else 0) * (if x ∈ U then b x else 0)) ≤
      2 * δ + δ ^ 2 := by
  apply two_terminal_hit_sum_le
    (fun x => if x ∈ U then a x else 0) (fun x => if x ∈ U then b x else 0) p q
  · simpa [hp] using ha
  · simpa [hq] using hb
  · have h := (countingSquareNorm_point_le (puncturedHit b U q) p).trans hbtail
    simpa [puncturedHit, hp, hpq] using h
  · have h := (countingSquareNorm_point_le (puncturedHit a U p) q).trans hatail
    simpa [puncturedHit, hq, hpq.symm] using h
  · apply (countingSquareNorm_mono (b := puncturedHit a U p) ?_).trans hatail
    intro x
    by_cases hx : x ∈ U <;> by_cases hxp : x = p <;> by_cases hxq : x = q <;>
      simp [awayFromTwo, puncturedHit, hx, hxp, hxq]
  · apply (countingSquareNorm_mono (b := puncturedHit b U q) ?_).trans hbtail
    intro x
    by_cases hx : x ∈ U <;> by_cases hxp : x = p <;> by_cases hxq : x = q <;>
      simp [awayFromTwo, puncturedHit, hx, hxp, hxq]

end CircleDomainRigidity

end

end OAI
