import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphContinuity
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace OAI

/-! # Coordinate continuity of the graph iteration

The backward tail is uniformly geometric.  Therefore continuity of each
forcing coordinate suffices, without continuity in the sequence sup norm.
Together with `continuous_contraction_observation`, this supplies the
continuity mechanism stated in the manuscript's graph construction.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

theorem continuous_stableBackward_coordinate
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (R : E →L[ℝ] E) (hR : ‖R‖ ≤ 1)
    (f : P → (ℕ →ᵇ E)) (C : ℝ) (hf : ∀ n, Continuous (fun p => f p n))
    (hbound : ∀ p, ‖f p‖ ≤ C) (n : ℕ) :
    Continuous (fun p => stableBackward R hR (f p) n) := by
  have hc : ∀ j : ℕ, Continuous (fun p =>
      (1 / 2 : ℝ) ^ j • (R ^ (j + 1)) (f p (n + j))) := by
    intro j
    exact continuous_const.smul ((R ^ (j + 1)).continuous.comp (hf (n + j)))
  have hs := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_right C
  have ht : Continuous (fun p => ∑' j : ℕ,
      (1 / 2 : ℝ) ^ j • (R ^ (j + 1)) (f p (n + j))) := by
    apply continuous_tsum hc hs
    intro j p
    exact (stableBackward_term_bound R hR (f p) n j).trans
      (mul_le_mul_of_nonneg_left (hbound p) (by positivity))
  exact ht.neg

theorem continuous_stableForward_coordinate
    {P E F : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : P → ℕ → E →L[ℝ] E) (B : P → ℕ → F →L[ℝ] E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ p n, ‖A p n‖ ≤ a) (hB : ∀ p n, ‖B p n‖ ≤ b)
    (w₀ : P → E) (w : P → (ℕ →ᵇ E)) (u : P → (ℕ →ᵇ F)) (r : P → (ℕ →ᵇ E))
    (hzero : Continuous w₀)
    (hAw : ∀ n, Continuous (fun p => A p n (w p n)))
    (hBu : ∀ n, Continuous (fun p => B p n (u p n)))
    (hr : ∀ n, Continuous (fun p => r p n)) (n : ℕ) :
    Continuous (fun p => stableForward (A p) (B p) a b ha hb (hA p) (hB p)
      (w₀ p) (w p) (u p) (r p) n) := by
  cases n with
  | zero => exact hzero
  | succ n => exact continuous_const.smul (((hAw n).add (hBu n)).add (hr n))

end DefocusingNLS

end OAI
