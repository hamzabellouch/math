import OAI.Analysis.Nonexpansive.TransmittedSubtreeErrors
import OAI.Analysis.Nonexpansive.TerminalSequence

namespace OAI

/-!
# Total displacement of the actual finite tree at the terminal sequence

The displacement through depth N is `terminalDefect (N+1)`.
The transmitted-subtree estimate only needs the internal part through depth
N-1.  Both are finite sums of actual generated-map displacements.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints
namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

theorem terminalDefect_nonneg {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {T : OrderedTree} {W : WeightedTree T} {K : Set X}
    (E : TreeEvaluation W K) (N : ℕ) (b : K) : 0 ≤ E.terminalDefect N b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Including the terminal level can only increase total displacement. -/
theorem terminalDefect_le_succ {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {T : OrderedTree} {W : WeightedTree T} {K : Set X}
    (E : TreeEvaluation W K) (N : ℕ) (b : K) :
    E.terminalDefect N b ≤ E.terminalDefect (N + 1) b := by
  rw [terminalDefect, terminalDefect, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- The total displacement of every fixed finite actual tree tends to zero on
its one common resolvent terminal sequence. -/
theorem terminalDefect_terminalSequence_tendsto
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (F : K → K) (hF : LipschitzWith 1 F)
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (hgenerated : ∀ k v, Generated hKclosed hKconvex F hF (E.map k v))
    (x : K) (N : ℕ) :
    Tendsto (fun j => E.terminalDefect N (terminalSequence hKclosed hKconvex F hF x j))
      atTop (𝓝 0) := by
  have hlim := tendsto_finsetSum (Finset.range N) fun k _ =>
    terminalSequence_finite_displacement_tendsto hKclosed hKconvex F hF hdiam
      (E.map k) (hgenerated k) x
  simpa only [terminalDefect, Finset.sum_const_zero] using hlim

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI
