import OAI.Analysis.LipschitzHilbert.Trees.UnaryRunCharging
import OAI.Analysis.LipschitzHilbert.Estimates.DisjointIntervalVariation

namespace OAI

/-! One common residual variation controls segments from every unary run. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)

theorem unaryRunSegment_intervals_disjoint (i j : UnaryRunSegment R P) (hij : i ≠ j) :
    i.2.val.2 ≤ j.2.val.1 ∨ j.2.val.2 ≤ i.2.val.1 := by
  by_cases hr : i.1 = j.1
  · rcases i with ⟨r,b⟩
    rcases j with ⟨s,c⟩
    dsimp only at hr hij ⊢
    subst s
    have hne : b.val ≠ c.val := by
      intro h
      have heq : b = c := Subtype.ext h
      exact hij (by cases heq; rfl)
    exact (P r).ordered b.val b.property c.val c.property hne
  · have hne : i.1.val ≠ j.1.val := fun h => hr (Subtype.ext h)
    have hbi := (P i.1).bounds i.2.val i.2.property
    have hbj := (P j.1).bounds j.2.val j.2.property
    rcases R.ordered i.1.val i.1.property j.1.val j.1.property hne with h | h
    · exact Or.inl (hbi.2.2.trans (h.trans hbj.1))
    · exact Or.inr (hbj.2.2.trans (h.trans hbi.1))

/-- The actual block-to-angular-level map preserves disjointness. Hence
all unary segments, including different runs, use a single variation bound. -/
theorem unary_runs_oscillation_cube_sum {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (level : ℕ → ℕ) (hlevel : StrictMono level) (N : ℕ)
    (hend : level finish ≤ N) :
    (∑ i : UnaryRunSegment R P,
      intervalOscillation F N (level i.2.val.1) (level i.2.val.2) ^ 3) ≤
      finiteCubicVariation (fun k => F (min k N)) (2 * N) := by
  apply disjoint_intervalOscillation_cube_sum F N
    (fun i : UnaryRunSegment R P => level i.2.val.1)
    (fun i : UnaryRunSegment R P => level i.2.val.2)
  · intro i
    exact hlevel ((P i.1).bounds i.2.val i.2.property).2.1
  · intro i
    have hb := (P i.1).bounds i.2.val i.2.property
    have hr := R.bounds i.1.val i.1.property
    exact (hlevel.monotone (hb.2.2.trans hr.2.2)).trans hend
  · intro i j hij
    exact (unaryRunSegment_intervals_disjoint R P i j hij).imp
      (fun h => hlevel.monotone h) (fun h => hlevel.monotone h)

end LipschitzHilbert

end

end OAI
