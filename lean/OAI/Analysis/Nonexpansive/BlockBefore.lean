import OAI.Analysis.Nonexpansive.SubtreeErrors
import OAI.Analysis.Nonexpansive.SwitchingScalar

namespace OAI

/-!
# The actual root output before switching a descendant block

We follow one node through the recursive nonlinear evaluation.  The other
child outputs contribute at most their total weight because they lie in a
set of diameter at most one.  The error along the chosen path is the actual
displacement of its ancestor maps at the comparison point.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- Separate one term of a normalized weighted sum.  Only the other terms
need to be bounded by one. -/
theorem weighted_focus_sum_le {ι : Type*} (s : Finset ι) (w D : ι → ℝ)
    (v : ι) (hv : v ∈ s)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hD : ∀ i ∈ s, i ≠ v → D i ≤ 1) :
    (∑ i ∈ s, w i * D i) ≤ w v * D v + (1 - w v) := by
  classical
  have hmass : (∑ i ∈ s.erase v, w i) + w v = 1 := by
    simpa only [hsum] using Finset.sum_erase_add s w hv
  have hoff : (∑ i ∈ s.erase v, w i * D i) ≤ ∑ i ∈ s.erase v, w i := by
    apply Finset.sum_le_sum
    intro i hi
    have his := (Finset.mem_erase.mp hi).2
    have hiv := (Finset.mem_erase.mp hi).1
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hD i his hiv) (hw i his)
  have hsplit := Finset.sum_erase_add s (fun i => w i * D i) hv
  linarith

namespace TreeEvaluation

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Sum the actual displacement at the proper ancestors of the selected node. -/
def pathDisplacement : (k : ℕ) → T.Node k → K → ℝ
  | 0, _, _ => 0
  | k + 1, v, z => pathDisplacement k (T.parent k v) z +
      ‖(E.map k (T.parent k v) z : X) - z‖

@[simp] theorem pathDisplacement_zero (v : T.Node 0) (z : K) :
    E.pathDisplacement 0 v z = 0 := rfl

@[simp] theorem pathDisplacement_succ (k : ℕ) (v : T.Node (k + 1)) (z : K) :
    E.pathDisplacement (k + 1) v z = E.pathDisplacement k (T.parent k v) z +
      ‖(E.map k (T.parent k v) z : X) - z‖ := rfl

/-- The same ancestor displacements weighted by their actual root path mass. -/
def weightedPathDisplacement : (k : ℕ) → T.Node k → K → ℝ
  | 0, _, _ => 0
  | k + 1, v, z => weightedPathDisplacement k (T.parent k v) z +
      W.pathWeight k (T.parent k v) * ‖(E.map k (T.parent k v) z : X) - z‖

@[simp] theorem weightedPathDisplacement_zero (v : T.Node 0) (z : K) :
    E.weightedPathDisplacement 0 v z = 0 := rfl

@[simp] theorem weightedPathDisplacement_succ (k : ℕ) (v : T.Node (k + 1)) (z : K) :
    E.weightedPathDisplacement (k + 1) v z =
      E.weightedPathDisplacement k (T.parent k v) z +
        W.pathWeight k (T.parent k v) * ‖(E.map k (T.parent k v) z : X) - z‖ := rfl

theorem pathDisplacement_nonneg (k : ℕ) (v : T.Node k) (z : K) :
    0 ≤ E.pathDisplacement k v z := by
  induction k with
  | zero => exact le_refl 0
  | succ k ih => exact add_nonneg (ih (T.parent k v)) (norm_nonneg _)

theorem weightedPathDisplacement_nonneg (k : ℕ) (v : T.Node k) (z : K) :
    0 ≤ E.weightedPathDisplacement k v z := by
  induction k with
  | zero => exact le_refl 0
  | succ k ih =>
      exact add_nonneg (ih (T.parent k v))
        (mul_nonneg (W.pathWeight_nonneg k _) (norm_nonneg _))

/-- Dropping path weights can only increase this sum of nonnegative errors. -/
theorem weightedPathDisplacement_le_pathDisplacement (k : ℕ) (v : T.Node k) (z : K) :
    E.weightedPathDisplacement k v z ≤ E.pathDisplacement k v z := by
  induction k with
  | zero => exact le_refl 0
  | succ k ih =>
      apply add_le_add (ih (T.parent k v))
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (W.pathWeight_le_one k (T.parent k v))
          (norm_nonneg ((E.map k (T.parent k v) z : X) - z))

/-- Focus one actual child while bounding all off-path child outputs by the
diameter of the set.  The node map is used only through nonexpansiveness. -/
theorem collapse_focus_norm_sub_le
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (k : ℕ) (H : T.Node (k + 1) → K) (v : T.Node (k + 1)) (z : K) :
    ‖(E.collapse k H (T.parent k v) : X) - z‖ ≤
      W.weight k v * ‖(H v : X) - z‖ + (1 - W.weight k v) +
        ‖(E.map k (T.parent k v) z : X) - z‖ := by
  classical
  have hsum := weighted_focus_sum_le
    (Finset.univ.filter (fun c => T.parent k c = T.parent k v))
    (W.weight k) (fun c => ‖(H c : X) - z‖) v (by simp)
    (fun c _ => W.weight_nonneg k c) (W.weight_sum k (T.parent k v))
    (fun c _ _ => hdiam (H c) z)
  exact (E.collapse_norm_sub_point_le k H z (T.parent k v)).trans
    (add_le_add_left hsum _)

/-- Follow one selected cutoff value through the actual nonlinear evaluation.
No affinity or positive lower bound on path weights is used. -/
theorem evaluate_focus_norm_sub_le
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (k : ℕ) (H : T.Node k → K) (v : T.Node k) (z : K) :
    ‖(E.evaluate k H : X) - z‖ ≤
      W.pathWeight k v * ‖(H v : X) - z‖ + (1 - W.pathWeight k v) +
        E.weightedPathDisplacement k v z := by
  induction k with
  | zero => simp [evaluate, weightedPathDisplacement, T.eq_root v]
  | succ k ih =>
      have hstep := E.collapse_focus_norm_sub_le hdiam k H v z
      calc
        ‖(E.evaluate (k + 1) H : X) - z‖ ≤
            W.pathWeight k (T.parent k v) *
              ‖(E.collapse k H (T.parent k v) : X) - z‖ +
              (1 - W.pathWeight k (T.parent k v)) +
                E.weightedPathDisplacement k (T.parent k v) z :=
          ih (E.collapse k H) (T.parent k v)
        _ ≤ W.pathWeight k (T.parent k v) *
              (W.weight k v * ‖(H v : X) - z‖ + (1 - W.weight k v) +
                ‖(E.map k (T.parent k v) z : X) - z‖) +
              (1 - W.pathWeight k (T.parent k v)) +
                E.weightedPathDisplacement k (T.parent k v) z :=
          add_le_add_left (add_le_add_left
            (mul_le_mul_of_nonneg_left hstep (W.pathWeight_nonneg k _)) _) _
        _ = W.pathWeight (k + 1) v * ‖(H v : X) - z‖ +
              (1 - W.pathWeight (k + 1) v) +
                E.weightedPathDisplacement (k + 1) v z := by
          rw [W.pathWeight_succ, E.weightedPathDisplacement_succ]
          ring

/-- The before-block root bound from the actual focused cutoff error and the
actual unweighted ancestor displacement budget. -/
theorem before_block_bound
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (k : ℕ) (H : T.Node k → K) (v : T.Node k) (z : K) {e : ℝ}
    (hfocused : ‖(H v : X) - z‖ ≤ e)
    (hpath : E.pathDisplacement k v z ≤ e) :
    ‖(E.evaluate k H : X) - z‖ ≤ 1 - W.pathWeight k v + 2 * e := by
  have he : 0 ≤ e := (norm_nonneg _).trans hfocused
  have hterm : W.pathWeight k v * ‖(H v : X) - z‖ ≤ e := by
    calc
      W.pathWeight k v * ‖(H v : X) - z‖ ≤ W.pathWeight k v * e :=
        mul_le_mul_of_nonneg_left hfocused (W.pathWeight_nonneg k v)
      _ ≤ 1 * e := mul_le_mul_of_nonneg_right (W.pathWeight_le_one k v) he
      _ = e := one_mul e
  have herr : E.weightedPathDisplacement k v z ≤ e :=
    (E.weightedPathDisplacement_le_pathDisplacement k v z).trans hpath
  have hfocus := E.evaluate_focus_norm_sub_le hdiam k H v z
  linarith

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI
