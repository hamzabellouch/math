import OAI.Analysis.Nonexpansive.OrderedGroupConcat
import OAI.Analysis.Nonexpansive.TreeFrontier

namespace OAI

/-!
# Assembling a frontier from its ordered parent groups

The local children are concatenated in parent order.  The inverse of the
actual concatenation equivalence retrieves each child's weight and map.
Reindexing the parent fiber proves normalization and identifies the actual
child average with its local group sum.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints.FrontierExtension

universe u v

/-- Read a local value using the unique group and position of a global index. -/
def groupValue {n : ℕ} (c : Fin n → ℕ) {V : Type v}
    (f : ∀ p, Fin (c p) → V) (i : Fin (OrderedGroupConcat.total c)) : V :=
  let s := (OrderedGroupConcat.equiv c).symm i
  f s.1 s.2

@[simp] theorem groupValue_group {n : ℕ} (c : Fin n → ℕ) {V : Type v}
    (f : ∀ p, Fin (c p) → V) (p : Fin n) (j : Fin (c p)) :
    groupValue c f (OrderedGroupConcat.group c p j) = f p j := by
  change (fun s : OrderedGroupConcat.Index c => f s.1 s.2)
    ((OrderedGroupConcat.equiv c).symm (OrderedGroupConcat.equiv c ⟨p, j⟩)) = f p j
  rw [Equiv.symm_apply_apply]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X}
variable (F : TreeFrontier K)
variable (childCount : Fin F.size → ℕ)
variable (count_pos : ∀ p, 0 < childCount p)
variable (childWeight : ∀ p, Fin (childCount p) → ℝ)
variable (weight_pos : ∀ p j, 0 < childWeight p j)
variable (weight_sum : ∀ p, ∑ j, childWeight p j = 1)
variable (childMap : ∀ p, Fin (childCount p) → K → K)
variable (map_nonexpansive : ∀ p j, LipschitzWith 1 (childMap p j))

/-- Assemble the actual extension from the positive, normalized child groups. -/
def ofGroups : FrontierExtension F where
  size := OrderedGroupConcat.total childCount
  size_pos := OrderedGroupConcat.total_pos childCount F.size_pos count_pos
  parent := OrderedGroupConcat.parent childCount
  parent_monotone := OrderedGroupConcat.parent_monotone childCount
  parent_surjective := OrderedGroupConcat.parent_surjective childCount count_pos
  weight := groupValue childCount childWeight
  weight_pos := fun i =>
    weight_pos ((OrderedGroupConcat.equiv childCount).symm i).1
      ((OrderedGroupConcat.equiv childCount).symm i).2
  weight_sum := by
    intro p
    rw [OrderedGroupConcat.sum_parent_fiber]
    simpa only [groupValue_group] using weight_sum p
  map := groupValue childCount childMap
  nonexpansive := fun i =>
    map_nonexpansive ((OrderedGroupConcat.equiv childCount).symm i).1
      ((OrderedGroupConcat.equiv childCount).symm i).2

@[simp] theorem ofGroups_size :
    (ofGroups F childCount count_pos childWeight weight_pos weight_sum
      childMap map_nonexpansive).size = OrderedGroupConcat.total childCount := rfl

@[simp] theorem ofGroups_parent (i : Fin (OrderedGroupConcat.total childCount)) :
    (ofGroups F childCount count_pos childWeight weight_pos weight_sum
      childMap map_nonexpansive).parent i = OrderedGroupConcat.parent childCount i := rfl

@[simp] theorem ofGroups_parent_group (p : Fin F.size) (j : Fin (childCount p)) :
    (ofGroups F childCount count_pos childWeight weight_pos weight_sum
      childMap map_nonexpansive).parent (OrderedGroupConcat.group childCount p j) = p :=
  OrderedGroupConcat.parent_group childCount p j

@[simp] theorem ofGroups_weight_group (p : Fin F.size) (j : Fin (childCount p)) :
    (ofGroups F childCount count_pos childWeight weight_pos weight_sum
      childMap map_nonexpansive).weight (OrderedGroupConcat.group childCount p j) =
      childWeight p j :=
  groupValue_group childCount childWeight p j

@[simp] theorem ofGroups_map_group (p : Fin F.size) (j : Fin (childCount p)) :
    (ofGroups F childCount count_pos childWeight weight_pos weight_sum
      childMap map_nonexpansive).map (OrderedGroupConcat.group childCount p j) =
      childMap p j :=
  groupValue_group childCount childMap p j

/-- The extension's actual parent fiber average is exactly the local group sum. -/
theorem ofGroups_childAverage_val
    (H : Fin (OrderedGroupConcat.total childCount) → K) (p : Fin F.size) :
    ((ofGroups F childCount count_pos childWeight weight_pos weight_sum
      childMap map_nonexpansive).childAverage H p : X) =
      ∑ j, childWeight p j • (H (OrderedGroupConcat.group childCount p j) : X) := by
  change (∑ i ∈ Finset.univ.filter
      (fun i => OrderedGroupConcat.parent childCount i = p),
      groupValue childCount childWeight i • (H i : X)) = _
  rw [OrderedGroupConcat.sum_parent_fiber]
  simp only [groupValue_group]

/-- Label every global child by its actual map applied to the common anchor. -/
theorem ofGroups_childAverage_map_val (x : K) (p : Fin F.size) :
    ((ofGroups F childCount count_pos childWeight weight_pos weight_sum
      childMap map_nonexpansive).childAverage
        (fun i => (ofGroups F childCount count_pos childWeight weight_pos weight_sum
          childMap map_nonexpansive).map i x) p : X) =
      ∑ j, childWeight p j • (childMap p j x : X) := by
  change (∑ i ∈ Finset.univ.filter
      (fun i => OrderedGroupConcat.parent childCount i = p),
      groupValue childCount childWeight i • (groupValue childCount childMap i x : X)) = _
  rw [OrderedGroupConcat.sum_parent_fiber]
  simp only [groupValue_group]

/-- Every local anchor return estimate is preserved by the assembled extension. -/
theorem ofGroups_childAverage_near (x : K) {τ : ℝ}
    (hreturn : ∀ p, ‖(∑ j, childWeight p j • (childMap p j x : X)) - (x : X)‖ < τ)
    (p : Fin F.size) :
    ‖((ofGroups F childCount count_pos childWeight weight_pos weight_sum
      childMap map_nonexpansive).childAverage
        (fun i => (ofGroups F childCount count_pos childWeight weight_pos weight_sum
          childMap map_nonexpansive).map i x) p : X) - (x : X)‖ < τ := by
  rw [ofGroups_childAverage_map_val]
  exact hreturn p

end ReflexiveFixedPoints.FrontierExtension

end

end OAI
