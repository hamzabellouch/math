import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.SupportCellRoot
import OAI.Analysis.RieszRectifiability.Nets.CellBadCountBounds
import OAI.Analysis.RieszRectifiability.Restart.CellRestartPacking

namespace OAI

/-!
# Restart coverage with a finite bad-cell budget

The iterated chart constant records the cost of assembling child charts. Induction
on the bad-cell budget covers points outside the restart remainders, since passing
a bad descendant reduces the remaining budget. Countable subadditivity then bounds
the uncovered mass by the original deficit and the sum of all remainder masses.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def badBudgetChartConstant (step : ℝ≥0 → ℝ≥0) : ℕ → ℝ≥0
  | 0 => step 1
  | b + 1 => step (badBudgetChartConstant step b)

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
  (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
  (Bad : SupportCellDescendant μ R hR k z → Prop)

variable (remainder parent : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d)) (next : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q})
  (step : ℝ≥0 → ℝ≥0)
  (hnext : ∀ q w, w ∈ next q → ∃ i : SupportCellDescendant μ R hR k z,
    q.val.depth ≤ i.depth ∧ i.cell ⊆ q.val.cell ∧ Bad i ∧
      i.depth < w.val.depth ∧ w.val.cell ⊆ i.cell)
  (hpartition : ∀ q, q.val.cell \ remainder q ⊆ parent q ∪
    ⋃ w : next q, w.val.val.cell)
  (hassemble : ∀ (q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}) (M : ℝ≥0)
    (child : ∀ w : next q, ball (0 : Ambient n) w.val.val.radius → Ambient d),
    (∀ w, LipschitzWith M (child w)) →
    (∀ w, Set.range (child w) ⊆ closedBall w.val.val.center (2 * w.val.val.radius)) →
    ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
      LipschitzWith (step M) g ∧ Set.range g ⊆ closedBall q.val.center (2 * q.val.radius) ∧
      parent q ⊆ Set.range g ∧
      ∀ w, w.val.val.cell ∩ Set.range (child w) ⊆ Set.range g)

include hnext hpartition hassemble

theorem exists_restart_chart_of_bad_budget (b : ℕ) (q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}) :
    ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
      LipschitzWith (badBudgetChartConstant step b) g ∧
      Set.range g ⊆ closedBall q.val.center (2 * q.val.radius) ∧
      ∀ x ∈ q.val.cell, cellBadCountBound Bad q.val b x →
        x ∉ ⋃ r : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}, remainder r → x ∈ Set.range g := by
  classical
  induction b generalizing q with
  | zero =>
    let child : ∀ w : next q, ball (0 : Ambient n) w.val.val.radius → Ambient d :=
      fun w _ => w.val.val.center
    have hlip (w : next q) : LipschitzWith 1 (child w) :=
      (LipschitzWith.const w.val.val.center).weaken (by norm_num)
    have himage (w : next q) : Set.range (child w) ⊆
        closedBall w.val.val.center (2 * w.val.val.radius) := by
      rintro y ⟨u, rfl⟩
      exact mem_closedBall_self (by positivity [w.val.val.radius_pos])
    obtain ⟨g, hg, hgrange, hparent, _⟩ := hassemble q 1 child hlip himage
    refine ⟨g, hg, hgrange, ?_⟩
    intro x hx hcount hnot
    have hr : x ∉ remainder q := fun hr => hnot (mem_iUnion.mpr ⟨q, hr⟩)
    have hpart : x ∈ parent q ∨ x ∈ ⋃ w : next q, w.val.val.cell :=
      hpartition q ⟨hx, hr⟩
    apply hpart.elim
    · intro hp
      exact hparent hp
    · intro hw
      obtain ⟨w, hxw⟩ := mem_iUnion.mp hw
      obtain ⟨i, hqi, hiq, hbad, _, hwi⟩ := hnext q w.val w.property
      exact False.elim ((cellBadCountBound_zero_forbids_bad_descendant
        Bad q.val i hqi hiq x (hwi hxw) hcount) hbad)
  | succ b ih =>
    have hc (w : next q) := ih w.val
    choose child hchildLip hchildRange hchildCover using hc
    obtain ⟨g, hg, hgrange, hparent, hchildren⟩ := hassemble q
      (badBudgetChartConstant step b) child hchildLip hchildRange
    refine ⟨g, hg, hgrange, ?_⟩
    intro x hx hcount hnot
    have hr : x ∉ remainder q := fun hr => hnot (mem_iUnion.mpr ⟨q, hr⟩)
    have hpart : x ∈ parent q ∨ x ∈ ⋃ w : next q, w.val.val.cell :=
      hpartition q ⟨hx, hr⟩
    apply hpart.elim
    · intro hp
      exact hparent hp
    · intro hw
      obtain ⟨w, hxw⟩ := mem_iUnion.mp hw
      obtain ⟨i, hqi, hiq, hbad, hiw, hwi⟩ := hnext q w.val w.property
      have hcount' := cellBadCountBound_descend_past_bad
        Bad q.val i w.val.val hqi hiq hbad hiw hwi b x hxw hcount
      exact hchildren w ⟨hxw, hchildCover w x hxw hcount' hnot⟩

theorem exists_restart_chart_with_original_mass_deficit (b : ℕ) (q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q})
    (A : Set (Ambient d))
    (hcount : ∀ x ∈ q.val.cell ∩ A, cellBadCountBound Bad q.val b x) :
    ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
      LipschitzWith (badBudgetChartConstant step b) g ∧
      Set.range g ⊆ closedBall q.val.center (2 * q.val.radius) ∧
      (q.val.cell ∩ A) \ (⋃ r : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}, remainder r) ⊆ Set.range g ∧
      μ (q.val.cell \ Set.range g) ≤ μ (q.val.cell \ A) + ∑' r : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}, μ (remainder r) := by
  let := supportCellDescendant_countable μ R hR k z
  obtain ⟨g, hg, hgrange, hcover⟩ := exists_restart_chart_of_bad_budget
    μ R hR k z Bad remainder parent next step hnext hpartition hassemble b q
  have hcovered : (q.val.cell ∩ A) \ (⋃ r : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}, remainder r) ⊆ Set.range g := by
    intro x hx
    exact hcover x hx.1.1 (hcount x hx.1) hx.2
  have hsub : q.val.cell \ Set.range g ⊆ (q.val.cell \ A) ∪ ⋃ r : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}, remainder r := by
    intro x hx
    by_cases ha : x ∈ A
    · right
      by_contra hn
      exact hx.2 (hcovered ⟨⟨hx.1, ha⟩, hn⟩)
    · exact Or.inl ⟨hx.1, ha⟩
  refine ⟨g, hg, hgrange, hcovered, ?_⟩
  exact ((measure_mono (μ := μ) hsub).trans (measure_union_le _ _)).trans
    (add_le_add le_rfl (measure_iUnion_le _))

end

end RieszRectifiability

end OAI
