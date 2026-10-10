import OAI.MeasureTheory.Falconer.Geometry.DyadicGeometry
import OAI.MeasureTheory.Falconer.Frostman.ContentBound
import OAI.MeasureTheory.Falconer.Frostman.Capacity
import Mathlib.MeasureTheory.OuterMeasure.OfFunction

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable def contentOuter {X : Type*} [EMetricSpace X]
    (s : ℝ) (hs : 0 < s) : OuterMeasure X :=
  OuterMeasure.ofFunction (fun U => (ediam U)^s)
    (by simp [ENNReal.zero_rpow_of_pos hs])

theorem contentOuter_apply {X : Type*} [EMetricSpace X]
    {s : ℝ} (hs : 0 < s) (U : Set X) :
    contentOuter s hs U = hausdorffContent s U := by
  rw [contentOuter, OuterMeasure.ofFunction_apply]
  rfl

theorem content_union_le {X : Type*} [EMetricSpace X]
    {s : ℝ} (hs : 0 < s) (U V : Set X) :
    hausdorffContent s (U ∪ V) ≤ hausdorffContent s U + hausdorffContent s V := by
  simpa only [← contentOuter_apply hs] using (measure_union_le (μ := contentOuter s hs) U V)

@[simp] theorem content_empty {X : Type*} [EMetricSpace X]
    {s : ℝ} (hs : 0 < s) : hausdorffContent s (∅ : Set X) = 0 := by
  rw [← contentOuter_apply hs]
  exact measure_empty

noncomputable def occupiedCapacity (E : Set Plane) (s : ℝ) (Q : DyadicSquare) : ℝ := by
  classical
  exact if (E ∩ Q.carrier).Nonempty then Q.side ^ s else 0

noncomputable def geometricTree (E : Set Plane) (s : ℝ) (Q : DyadicSquare) :
    ℕ → CapacityTree
  | 0 => .leaf (occupiedCapacity E s Q)
  | K+1 => .node (occupiedCapacity E s Q)
      (geometricTree E s (Q.child false false) K)
      (geometricTree E s (Q.child false true) K)
      (geometricTree E s (Q.child true false) K)
      (geometricTree E s (Q.child true true) K)

theorem occupiedCapacity_nonneg (E : Set Plane) (s : ℝ)
    (Q : DyadicSquare) (hQ : 0 ≤ Q.side) : 0 ≤ occupiedCapacity E s Q := by
  unfold occupiedCapacity
  split_ifs <;> positivity

theorem geometricTree_nonnegative (E : Set Plane) (s : ℝ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (K : ℕ) :
    (geometricTree E s Q K).nonnegative := by
  induction K generalizing Q with
  | zero => exact occupiedCapacity_nonneg E s Q hQ.le
  | succ K ih =>
    exact ⟨occupiedCapacity_nonneg E s Q hQ.le,
      ih _ (Q.child_side_pos hQ _ _), ih _ (Q.child_side_pos hQ _ _),
      ih _ (Q.child_side_pos hQ _ _), ih _ (Q.child_side_pos hQ _ _)⟩

theorem content_le_occupiedCapacity (E : Set Plane) {s : ℝ} (hs : 0 < s)
    (Q : DyadicSquare) (hQ : 0 < Q.side) :
    hausdorffContent s (E ∩ Q.carrier) ≤
      ENNReal.ofReal ((2 : ℝ)^s * occupiedCapacity E s Q) := by
  classical
  by_cases h : (E ∩ Q.carrier).Nonempty
  · rw [occupiedCapacity, ite_eq_left h, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hQ.le]
    calc
      hausdorffContent s (E ∩ Q.carrier) ≤ (ediam (E ∩ Q.carrier))^s :=
        content_le_diameter hs _
      _ ≤ (ENNReal.ofReal (2 * Q.side))^s :=
        ENNReal.rpow_le_rpow ((ediam_mono inter_subset_right).trans (Q.ediam_le hQ.le)) hs.le
      _ = ENNReal.ofReal ((2 * Q.side)^s) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.le]
  · rw [not_nonempty_iff_eq_empty.mp h, content_empty hs,
      occupiedCapacity, ite_eq_right h, mul_zero, ENNReal.ofReal_zero]

theorem content_le_children (E : Set Plane) {s : ℝ} (hs : 0 < s)
    (Q : DyadicSquare) :
    hausdorffContent s (E ∩ Q.carrier) ≤
      hausdorffContent s (E ∩ (Q.child false false).carrier) +
      hausdorffContent s (E ∩ (Q.child false true).carrier) +
      hausdorffContent s (E ∩ (Q.child true false).carrier) +
      hausdorffContent s (E ∩ (Q.child true true).carrier) := by
  rw [Q.cover_children, inter_union_distrib_left,
    inter_union_distrib_left, inter_union_distrib_left]
  exact (content_union_le hs _ _).trans (by
    have h0 := content_union_le hs (E ∩ (Q.child false false).carrier)
      (E ∩ (Q.child false true).carrier)
    have h1 := content_union_le hs (E ∩ (Q.child true false).carrier)
      (E ∩ (Q.child true true).carrier)
    simpa only [add_assoc] using add_le_add h0 h1)

theorem content_le_geometric_effective (E : Set Plane) {s : ℝ} (hs : 0 < s)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (K : ℕ) :
    hausdorffContent s (E ∩ Q.carrier) ≤
      ENNReal.ofReal ((2 : ℝ)^s * (geometricTree E s Q K).effective) := by
  induction K generalizing Q with
  | zero => exact content_le_occupiedCapacity E hs Q hQ
  | succ K ih =>
    have hn (i j : Bool) := effective_nonnegative
      (geometricTree_nonnegative E s (Q.child i j) (Q.child_side_pos hQ i j) K)
    have hsum := add_le_add
      (add_le_add (add_le_add (ih _ (Q.child_side_pos hQ false false))
        (ih _ (Q.child_side_pos hQ false true)))
        (ih _ (Q.child_side_pos hQ true false)))
        (ih _ (Q.child_side_pos hQ true true))
    have hcost := (content_le_children E hs Q).trans hsum
    simp only [geometricTree, CapacityTree.effective]
    have h00 := hn false false
    have h01 := hn false true
    have h10 := hn true false
    have h11 := hn true true
    have hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        ENNReal.ofReal ((2 : ℝ)^s * (a+b)) =
          ENNReal.ofReal ((2 : ℝ)^s*a) + ENNReal.ofReal ((2 : ℝ)^s*b) := by
      intro a b ha hb
      rw [mul_add, ENNReal.ofReal_add (by positivity) (by positivity)]
    by_cases h : occupiedCapacity E s Q ≤
        (geometricTree E s (Q.child false false) K).effective +
        (geometricTree E s (Q.child false true) K).effective +
        (geometricTree E s (Q.child true false) K).effective +
        (geometricTree E s (Q.child true true) K).effective
    · rw [min_eq_left h]
      exact content_le_occupiedCapacity E hs Q hQ
    · rw [min_eq_right (le_of_not_ge h), hadd _ _ (by positivity) h11,
        hadd _ _ (by positivity) h10, hadd _ _ h00 h01]
      exact hcost

theorem exists_uniform_geometric_routes (E : Set Plane) (hE : IsCompact E)
    {s : ℝ≥0} (hs : 0 < s) (hd : (s : ℝ≥0∞) < dimH E)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (hEQ : E ⊆ Q.carrier) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, Routes (geometricTree E s Q K) c := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hp := content_positive_of_lt_dimH E hs hd
  have hf := content_finite_of_bounded hs' hE.isBounded
  have hF : 0 < (2 : ℝ)^(s : ℝ) := by positivity
  let c := (hausdorffContent (s : ℝ) E).toReal / (2 : ℝ)^(s : ℝ)
  have hc : 0 < c := div_pos (ENNReal.toReal_pos (ne_of_gt hp) (ne_of_lt hf)) hF
  refine ⟨c,hc,fun K => routes_of_le_effective _
    (geometricTree_nonnegative E s Q hQ K) c hc.le ?_⟩
  have hb := content_le_geometric_effective E hs' Q hQ K
  rw [inter_eq_left.mpr hEQ] at hb
  have hn := effective_nonnegative (geometricTree_nonnegative E s Q hQ K)
  have hr := ENNReal.toReal_mono (by simp :
    ENNReal.ofReal ((2 : ℝ)^(s : ℝ) * (geometricTree E s Q K).effective) ≠ ∞) hb
  rw [ENNReal.toReal_ofReal (mul_nonneg hF.le hn)] at hr
  exact (div_le_iff₀ hF).mpr (by simpa only [mul_comm] using hr)

end PlanarFalconer

end OAI
