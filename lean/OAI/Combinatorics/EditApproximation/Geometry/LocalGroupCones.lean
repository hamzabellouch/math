import OAI.Combinatorics.EditApproximation.Geometry.CellGroupSelection
import OAI.Combinatorics.EditApproximation.Geometry.LocalRefinementCones
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Cell-keyed shared draws permit direct local group enumeration. The
complete and local finite programs use the same draw at every cell label. -/

namespace EditApproximation

theorem targetCell_of_cellTargetStates {n g : ℕ} {side : ℚ}
    (cell : ℕ × ℕ) (hg : 0 < g) (hside : 0 < side) (r : TargetInterval n)
    (hr : r ∈ cellTargetStates n g side cell) : targetCell side r = cell := by
  have hc := (cellTargetStates_mem cell hg r).mp hr
  apply Prod.ext
  · apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hside.le)).2
    exact ⟨(le_div_iff₀ hside).2 hc.2.2.1, (div_lt_iff₀ hside).2 hc.2.2.2.1⟩
  · apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hside.le)).2
    exact ⟨(le_div_iff₀ hside).2 hc.2.2.2.2.1, (div_lt_iff₀ hside).2 hc.2.2.2.2.2⟩

theorem chooseCellGroupAction_center {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (action : PhysicalRationalAction M target.length)
    (hselected : chooseCellGroupAction source target parent b P F exponent Q tau a
      parentInitial child initial current cell draw = some action) :
    action.center ∈ cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(exponent : ℤ))) cell := by
  unfold chooseCellGroupAction at hselected
  dsimp only at hselected
  split_ifs at hselected with hempty
  have heq := Option.some.inj hselected
  rw [← heq]
  exact (unskippedBandList_mem_iff _ _).mp
    (chooseUnskippedGroup_spec Q current _ hempty draw).1

def representativeCells {n : ℕ} (N P F b : ℕ) (a theta : ℚ)
    (initial : TargetInterval n → ℚ) : List (ℕ × ℕ) :=
  (((representativeList N P F a initial).filter fun br => decide (br.1 = b)).map
    fun br => targetCell (theta * b) br.2).eraseDups

theorem representativeCells_mem {n N P F b : ℕ} (a theta : ℚ)
    (initial : TargetInterval n → ℚ) (r : TargetInterval n)
    (hr : (b, r) ∈ representativeList N P F a initial) :
    targetCell (theta * b) r ∈ representativeCells N P F b a theta initial := by
  apply List.mem_eraseDups.mpr
  apply List.mem_map.mpr
  exact ⟨(b, r), List.mem_filter.mpr ⟨hr, by simp⟩, rfl⟩



section CellPrograms

variable {α : Type*} {M : ℕ} (source target : List α)
  (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial current : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q)

local notation "theta" => (2 : ℚ) ^ (-(exponent : ℤ))

def completeCellGroupActions : List (PhysicalRationalAction M target.length) :=
  (dyadicScales N).flatMap fun b =>
    (representativeCells N P F b a theta parentInitial).filterMap fun cell =>
      chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial
        child initial current cell (draw b cell)



theorem cellGroupAction_location (b : ℕ) (hb : b ∈ dyadicScales N) (cell : ℕ × ℕ)
    (action : PhysicalRationalAction M target.length)
    (hselected : chooseCellGroupAction source target parent b P F exponent Q tau a
      parentInitial child initial current cell (draw b cell) = some action) :
    (b, action.center) ∈ representativeList N P F a parentInitial ∧
      targetCell (theta * b) action.center = cell := by
  have hcenter := chooseCellGroupAction_center source target parent b P F exponent Q tau a
    parentInitial child initial current cell (draw b cell) action hselected
  have hrep := cellRepresentativeStates_mem_representatives a parentInitial theta cell action.center hb hcenter
  have hbpos : 0 < b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb
    positivity
  have hcell := (List.mem_filter.mp hcenter).1
  exact ⟨hrep, targetCell_of_cellTargetStates cell (by unfold seedGridSpacing; omega)
    (by positivity) action.center hcell⟩

theorem localCellGroupActions_subset (q : TargetInterval target.length) :
    ∀ action ∈ localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q,
      action ∈ completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw := by
  intro action ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp ha
  have hb' := (List.mem_filter.mp hb).1
  have hlocation := cellGroupAction_location source target parent N P F exponent Q tau a
    parentInitial child initial current draw b hb' cell action hselected
  have hcell := representativeCells_mem a theta parentInitial action.center hlocation.1
  rw [hlocation.2] at hcell
  exact List.mem_flatMap.mpr ⟨b, hb', List.mem_filterMap.mpr ⟨cell, hcell, hselected⟩⟩

theorem completeCellGroupActions_wide :
    ∀ action ∈ completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw,
      action ∈ rationalActualWideActions parent (representativeList N P F a parentInitial) P := by
  intro action ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp ha
  exact chooseCellGroupAction_wide_mem source target parent N b P F exponent Q tau a parentInitial
    child initial current cell (draw b cell) hb action hselected

/-- All improving complete cell cones occur in the bounded local cell
program. Identical cell keys use identical shared samples. -/
theorem localCellGroupMinimum_eq (q : TargetInterval target.length) (fallback : ℚ)
    (ha : 1 ≤ a) (hF : 1 ≤ F) (hfallback : fallback ≤ parentInitial q)
    (hcurrent : ∀ i r, 0 ≤ current i r)
    (hspatial : ∀ r, |parentInitial q - parentInitial r| ≤ 32 * F * targetEndpointDistance q r) :
    rationalMinimum fallback
        ((localCellGroupActions source target parent N P F exponent Q tau a parentInitial
          child initial current draw q).map
          (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
            (fun is => current is.1 is.2) q)) =
      rationalMinimum fallback
        ((completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
          child initial current draw).map
          (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
            (fun is => current is.1 is.2) q)) := by
  apply rationalMinimum_local_complete_lt
    _ _ _ fallback (localCellGroupActions_subset source target parent N P F exponent Q tau a
      parentInitial child initial current draw q)
  intro action haction hvalue
  have hwide := completeCellGroupActions_wide source target parent N P F exponent Q tau a
    parentInitial child initial current draw action haction
  have hcharge := rationalActionValue_pruned_lower (fun q r => targetEndpointDistance q r)
    (128 * (F : ℚ)) (fun is => current is.1 is.2) q action
    (128 * (F : ℚ) * targetEndpointDistance q action.center) le_rfl
    (rationalActualWideActions_connection_nonneg parent _ P action hwide) (fun i => hcurrent _ _)
  have hw : 0 < parentInitial q := by
    have hnonneg : (0 : ℚ) ≤ 128 * (F : ℚ) * targetEndpointDistance q action.center := by positivity
    exact hnonneg.trans_lt ((hcharge.trans_lt hvalue).trans_le hfallback)
  obtain ⟨b, hb, haction⟩ := List.mem_flatMap.mp haction
  obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp haction
  have hlocation := cellGroupAction_location source target parent N P F exponent Q tau a
    parentInitial child initial current draw b hb cell action hselected
  have hconditions := representativeList_conditions a parentInitial hlocation.1
  have hnumeric := refinement_cone_locality_numeric hw ha (show (1 : ℚ) ≤ F by exact_mod_cast hF)
    (Nat.cast_nonneg (α := ℚ) (targetEndpointDistance q action.center)) (hspatial action.center)
    hconditions.2.2.2 le_rfl ((hcharge.trans hvalue.le).trans hfallback)
  have hdist : targetEndpointDistance q action.center ≤ ⌈parentInitial q⌉₊ := by
    exact_mod_cast hnumeric.2.2.trans (Nat.le_ceil _)
  have hbpos : 0 < b := by obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb; positivity
  have hcell := localTargetCells_complete (theta * b) (by positivity) ⌈parentInitial q⌉₊ q action.center
    (by unfold targetEndpointDistance at hdist; omega) (by unfold targetEndpointDistance at hdist; omega)
  rw [hlocation.2] at hcell
  apply List.mem_flatMap.mpr
  refine ⟨b, List.mem_filter.mpr ⟨hb, decide_eq_true ⟨hnumeric.1, hnumeric.2.1⟩⟩, ?_⟩
  exact List.mem_filterMap.mpr ⟨cell, hcell, hselected⟩

end CellPrograms

end EditApproximation

end OAI
