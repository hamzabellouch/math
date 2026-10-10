import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Score
import OAI.Probability.CriticalPercolation.ProductMeasure.CoordinateNeDensity

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E] [DecidableEq E]

theorem score_congr_support (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ) (hf : LazyDFS.Fresh w p used)
    (F F' : Set E → Prop) (hF : ∀ ω, density w ω ≠ 0 → (F ω ↔ F' ω))
    (ω : Set E) (hω : density w ω ≠ 0) : T.score p F w ω = T.score p F' w ω := by
  induction T generalizing used w with
  | done r => rfl
  | ask e l r hl hr =>
    have hb := hf e hT.1
    have h0 : w e False ≠ 0 := by rw [hb.1]; exact (sub_pos.mpr hp.2).ne'
    have h1 : w e True ≠ 0 := by rw [hb.2]; exact hp.1.ne'
    have hd := delta_congr_support w e h0 h1 F F' hF
    have hP := openPivot_congr_support w e h0 F F' hF ω hω
    dsimp only [score]
    erw [hP,hd]
    congr 1
    by_cases he : ω e
    · rw [ite_eq_left he,ite_eq_left he]
      apply hr (insert e used) hT.2.2 (pin w e True) (LazyDFS.fresh_pin w p used hf e True)
      · intro ω' hω'
        exact hF ω' (density_pin_old_support w e True ω' h1 hω')
      · exact density_pin_of_support w ω e True hω (propext (iff_true_intro he))
    · rw [ite_eq_right he,ite_eq_right he]
      apply hl (insert e used) hT.2.1 (pin w e False) (LazyDFS.fresh_pin w p used hf e False)
      · intro ω' hω'
        exact hF ω' (density_pin_old_support w e False ω' h0 hω')
      · exact density_pin_of_support w ω e False hω (propext (iff_false_intro he))

end CriticalPercolation.SearchTree

end
end

end OAI
