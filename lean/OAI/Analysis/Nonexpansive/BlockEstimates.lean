import OAI.Analysis.Nonexpansive.BlockBefore
import OAI.Analysis.Nonexpansive.SwitchingBlocks
import OAI.Analysis.Nonexpansive.TransmittedSubtreeErrors

namespace OAI

/-!
# Detection of actual switched descendant blocks

The before and after estimates are proved for the actual root states.  The
ideal cutoff contains labels strictly to the left and the common terminal
point elsewhere.  Its identification with an earlier prediction is supplied
by the candidate construction, after which the terminal detector applies.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints
namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- The ideal state at a cutoff immediately after a whole block has switched. -/
def idealCutoff (k : ℕ) (x b : K) (v : T.Node k) : T.Node k → K :=
  fun u => if u < v then E.map k u x else b

/-- The actual before-block root is close to the selected node's label. -/
theorem beforeBlock_norm_sub_label_le
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1)
    (x b : K) (τ : ℕ → ℝ) {k N : ℕ} (h : k ≤ N) (v : T.Node k)
    (haverage : ∀ d, d < N → ∀ p : T.Node d,
      ‖(E.childAverage d (fun c => E.map (d + 1) c x) p : X) - x‖ ≤ τ d)
    {e : ℝ} (htail : (∑ d ∈ Finset.Ico k N, τ d) ≤ e)
    (hpath : E.pathDisplacement k v (E.map k v x) ≤ e) :
    ‖(E.beforeBlock h (fun s => E.map N s x) b v : X) - E.map k v x‖ ≤
      1 - W.pathWeight k v + 2 * e := by
  unfold beforeBlock switchRoot
  rw [E.evaluate_subtreeOutput h]
  apply E.before_block_bound hdiam k _ v (E.map k v x)
  · refine (E.subtreeOutput_untouched_norm_sub_le x τ haverage h
      (E.switchLeaves N (fun s => E.map N s x) b (T.descendantHi h v)) v ?_).trans htail
    intro s hs
    exact E.switchLeaves_beforeBlock_of_descendant h (fun s => E.map N s x) b v s hs
  · exact hpath

/-- Uniform errors of untouched and transmitted subtrees give the actual
post-block root's distance from its ideal cutoff evaluation. -/
theorem afterBlock_norm_sub_ideal_le
    (x b : K) (τ : ℕ → ℝ) {k N : ℕ} (h : k ≤ N) (v : T.Node k)
    (haverage : ∀ d, d < N → ∀ p : T.Node d,
      ‖(E.childAverage d (fun c => E.map (d + 1) c x) p : X) - x‖ ≤ τ d)
    {e : ℝ} (htail : (∑ d ∈ Finset.Ico k N, τ d) ≤ e)
    (hterminal : E.terminalDefect N b ≤ e) :
    ‖(E.afterBlock h (fun s => E.map N s x) b v : X) -
      E.evaluate k (E.idealCutoff k x b v)‖ ≤ e := by
  unfold afterBlock switchRoot
  rw [E.evaluate_subtreeOutput h]
  apply E.evaluate_norm_sub_le_of_forall
  intro u
  by_cases huv : u < v
  · simp only [idealCutoff, ite_eq_left huv]
    refine (E.subtreeOutput_untouched_norm_sub_le x τ haverage h
      (E.switchLeaves N (fun s => E.map N s x) b (T.descendantLo h v)) u ?_).trans htail
    intro s hs
    rw [E.switchLeaves_afterBlock h (fun s => E.map N s x) b v s, hs, ite_eq_left huv]
  · simp only [idealCutoff, ite_eq_right huv]
    refine (E.subtreeOutput_norm_sub_le_terminalDefect h
      (E.switchLeaves N (fun s => E.map N s x) b (T.descendantLo h v)) b u ?_).trans hterminal
    intro s hs
    have hsu := (T.mem_descendants h u s).mp hs
    rw [E.switchLeaves_afterBlock h (fun s => E.map N s x) b v s, hsu, ite_eq_right huv]

/-- The exact `W_v - 5e_v` lower bound for an actual before-minus-after block
increment, proved from the actual child averages and ancestor displacements. -/
theorem actual_block_detection
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1)
    (x b : K) (τ : ℕ → ℝ) {k N : ℕ} (h : k ≤ N) (v : T.Node k)
    (haverage : ∀ d, d < N → ∀ p : T.Node d,
      ‖(E.childAverage d (fun c => E.map (d + 1) c x) p : X) - x‖ ≤ τ d)
    (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) {e : ℝ}
    (htail : (∑ d ∈ Finset.Ico k N, τ d) ≤ e)
    (hpath : E.pathDisplacement k v (E.map k v x) ≤ e)
    (hterminal : E.terminalDefect N b ≤ e)
    (hdetect : 1 - 2 * e ≤
      f ((E.map k v x : X) - E.evaluate k (E.idealCutoff k x b v))) :
    W.pathWeight k v - 5 * e ≤
      f ((E.beforeBlock h (fun s => E.map N s x) b v : X) -
        E.afterBlock h (fun s => E.map N s x) b v) := by
  exact block_detection_of_norm_bounds f hf
    (E.beforeBlock h (fun s => E.map N s x) b v)
    (E.afterBlock h (fun s => E.map N s x) b v)
    (E.map k v x) (E.evaluate k (E.idealCutoff k x b v))
    (W.pathWeight k v) e hdetect
    (E.beforeBlock_norm_sub_label_le hdiam x b τ h v haverage htail hpath)
    (E.afterBlock_norm_sub_ideal_le x b τ h v haverage htail hterminal)

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI
