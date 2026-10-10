import OAI.Analysis.Nonexpansive.TreeEvaluation
import OAI.Analysis.Nonexpansive.SwitchingNorm
import Mathlib.Algebra.BigOperators.Intervals
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Actual root states during right-to-left switching

At cutoff `t`, the leaves with index strictly below `t` retain their labels;
all other leaves have the common terminal value.  Decreasing `t` by one is one
actual switch.  Every increment below is a difference of these evaluated root
states, so finite telescoping never assumes that a node map is linear.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints
namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- The actual leaf assignment after every leaf at or to the right of the
cutoff has switched. -/
def switchLeaves (_E : TreeEvaluation W K) (N : ℕ) (y : T.Node N → K)
    (b : K) (t : ℕ) : T.Node N → K :=
  fun s => if s.val < t then y s else b

/-- One fully evaluated actual root state of the switching experiment. -/
noncomputable def switchRoot (N : ℕ) (y : T.Node N → K) (b : K) (t : ℕ) : K :=
  E.evaluate N (E.switchLeaves N y b t)

@[simp] theorem switchLeaves_zero (N : ℕ) (y : T.Node N → K) (b : K) :
    E.switchLeaves N y b 0 = fun _ => b := by
  funext s
  simp [switchLeaves]

@[simp] theorem switchLeaves_full (N : ℕ) (y : T.Node N → K) (b : K) :
    E.switchLeaves N y b (T.size N) = y := by
  funext s
  simp [switchLeaves, s.isLt]

/-- Two consecutive cutoff states differ only at the leaf being switched. -/
theorem switchLeaves_succ_eq_of_ne (N : ℕ) (y : T.Node N → K) (b : K)
    (s w : T.Node N) (hws : w ≠ s) :
    E.switchLeaves N y b (s.val + 1) w = E.switchLeaves N y b s.val w := by
  have hv : w.val ≠ s.val := fun h => hws (Fin.ext h)
  have hc : (w.val < s.val + 1) ↔ (w.val < s.val) := by omega
  simp only [switchLeaves, hc]

/-- The root increment of one leaf has its actual path weight as its norm
bound. -/
theorem switchRoot_single_norm_le (N : ℕ) (y : T.Node N → K) (b : K)
    (s : T.Node N) :
    ‖(E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val‖ ≤
      W.pathWeight N s * ‖(y s : X) - b‖ := by
  have h := E.evaluate_norm_sub_le_single N
    (E.switchLeaves N y b (s.val + 1)) (E.switchLeaves N y b s.val) s
    (fun w hw => E.switchLeaves_succ_eq_of_ne N y b s w hw)
  simpa only [switchRoot, switchLeaves, Nat.lt_succ_self, ite_true,
    lt_self_iff_false, ite_false] using h

/-- Diameter one bounds the actual single-leaf root increment by its weight. -/
theorem switchRoot_single_norm_le_weight (N : ℕ) (y : T.Node N → K) (b : K)
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1) (s : T.Node N) :
    ‖(E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val‖ ≤
      W.pathWeight N s := by
  refine (E.switchRoot_single_norm_le N y b s).trans ?_
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hdiam (y s) b) (le_of_lt (W.pathWeight_pos N s))

/-- The normalized difference associated to a single actual leaf switch. -/
noncomputable def switchVector (N : ℕ) (y : T.Node N → K) (b : K)
    (s : T.Node N) : X :=
  (W.pathWeight N s)⁻¹ •
    ((E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val)

/-- The actual normalized switch vector lies in the whole unit ball of any
subspace containing all differences of points in K. -/
theorem switchVector_mem_norm_reconstruct (N : ℕ) (y : T.Node N → K) (b : K)
    (Y : Submodule ℝ X) (hY : ∀ a c : K, (a : X) - c ∈ Y)
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1) (s : T.Node N) :
    E.switchVector N y b s ∈ Y ∧ ‖E.switchVector N y b s‖ ≤ 1 ∧
      W.pathWeight N s • E.switchVector N y b s =
        (E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val := by
  exact normalized_switch_difference Y
    (E.switchRoot N y b (s.val + 1)) (E.switchRoot N y b s.val)
    (W.pathWeight N s) (W.pathWeight_pos N s)
    (hY _ _) (E.switchRoot_single_norm_le_weight N y b hdiam s)

/-- Consecutive actual root outputs telescope over a half-open interval.
No node map is moved through the sum. -/
theorem switchRoot_interval_telescope (N : ℕ) (y : T.Node N → K) (b : K)
    {lo hi : ℕ} (h : lo ≤ hi) :
    (∑ i ∈ Finset.Ico lo hi,
      ((E.switchRoot N y b (i + 1) : X) - E.switchRoot N y b i)) =
        (E.switchRoot N y b hi : X) - E.switchRoot N y b lo := by
  exact Finset.sum_Ico_sub (fun i => (E.switchRoot N y b i : X)) h

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI
