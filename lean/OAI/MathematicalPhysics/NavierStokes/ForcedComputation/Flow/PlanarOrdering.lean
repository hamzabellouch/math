import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarParking

namespace OAI

/-! Effective source and target orders for the finite planar processor.
Extraction goes from right to left; insertion goes from left to right. The
orders are stable merge sorts of rational centers, including tied centers. -/

namespace ForcedComputation.PlanarRouting

open ShearFlows

def sortBy {α : Type*} (key : α → ℚ) (xs : List α) : List α :=
  xs.mergeSort (fun a b => decide (key a ≤ key b))

theorem sortBy_perm {α : Type*} (key : α → ℚ) (xs : List α) :
    List.Perm (sortBy key xs) xs := List.mergeSort_perm _ _

theorem sortBy_length {α : Type*} (key : α → ℚ) (xs : List α) :
    (sortBy key xs).length = xs.length := (sortBy_perm key xs).length_eq

theorem mem_sortBy {α : Type*} (key : α → ℚ) (xs : List α) (x : α) :
    x ∈ sortBy key xs ↔ x ∈ xs := (sortBy_perm key xs).mem_iff

theorem sortBy_pairwise {α : Type*} (key : α → ℚ) (xs : List α) :
    (sortBy key xs).Pairwise (fun a b => key a ≤ key b) := by
  let r : α → α → Prop := fun a b => key a ≤ key b
  let : Std.Total r := ⟨fun a b => le_total (key a) (key b)⟩
  let : IsTrans α r := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
  exact List.pairwise_mergeSort' r xs

theorem sortBy_get_le {α : Type*} (key : α → ℚ) (xs : List α)
    {i j : Fin (sortBy key xs).length} (hij : i < j) :
    key ((sortBy key xs).get i) ≤ key ((sortBy key xs).get j) :=
  (sortBy_pairwise key xs).rel_get_of_lt hij

theorem sortBy_nodup {α : Type*} (key : α → ℚ) {xs : List α} (h : xs.Nodup) :
    (sortBy key xs).Nodup := (sortBy_perm key xs).nodup_iff.mpr h

def rank {α : Type*} [DecidableEq α] (key : α → ℚ) (xs : List α) (x : α)
    (hx : x ∈ xs) : Fin (sortBy key xs).length :=
  ⟨(sortBy key xs).idxOf x, List.idxOf_lt_length_of_mem ((mem_sortBy key xs x).mpr hx)⟩

theorem get_rank {α : Type*} [DecidableEq α] (key : α → ℚ) (xs : List α) (x : α)
    (hx : x ∈ xs) : (sortBy key xs).get (rank key xs x hx) = x :=
  List.idxOf_get _

theorem rank_injective {α : Type*} [DecidableEq α] (key : α → ℚ) (xs : List α)
    {x y : α} (hx : x ∈ xs) (hy : y ∈ xs)
    (hxy : rank key xs x hx = rank key xs y hy) : x = y := by
  have h := congrArg (sortBy key xs).get hxy
  simpa only [get_rank] using h

end ForcedComputation.PlanarRouting

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting

def sourceOrder (M : Alternating.Machine) (hM : M.WellFormed) :
    List (Branch (finiteMachine M hM)) :=
  letI := ShearFlows.neZeroTwo
  sortBy (fun b => -centerQ (instruction M hM b).source 0) (geometricBranches M hM)

def targetOrder (M : Alternating.Machine) (hM : M.WellFormed) :
    List (Branch (finiteMachine M hM)) :=
  letI := ShearFlows.neZeroTwo
  sortBy (fun b => centerQ (instruction M hM b).target 0) (geometricBranches M hM)

theorem sourceOrder_perm (M : Alternating.Machine) (hM : M.WellFormed) :
    List.Perm (sourceOrder M hM) (geometricBranches M hM) := sortBy_perm _ _

theorem targetOrder_perm (M : Alternating.Machine) (hM : M.WellFormed) :
    List.Perm (targetOrder M hM) (geometricBranches M hM) := sortBy_perm _ _

theorem sourceOrder_nodup (M : Alternating.Machine) (hM : M.WellFormed) :
    (sourceOrder M hM).Nodup :=
  (sourceOrder_perm M hM).nodup_iff.mpr (List.nodup_dedup _)

theorem targetOrder_nodup (M : Alternating.Machine) (hM : M.WellFormed) :
    (targetOrder M hM).Nodup :=
  (targetOrder_perm M hM).nodup_iff.mpr (List.nodup_dedup _)

theorem sourceOrder_complete (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : b ∈ sourceOrder M hM := by
  apply (sourceOrder_perm M hM).mem_iff.mpr
  simpa only [geometricBranches, List.mem_dedup] using mem_compileBranches M hM b

theorem targetOrder_complete (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : b ∈ targetOrder M hM := by
  apply (targetOrder_perm M hM).mem_iff.mpr
  simpa only [geometricBranches, List.mem_dedup] using mem_compileBranches M hM b

theorem sourceOrder_centers (M : Alternating.Machine) (hM : M.WellFormed)
    {i j : Fin (sourceOrder M hM).length} (hij : i < j) :
    (instruction M hM ((sourceOrder M hM).get j)).source.center 0 ≤
      (instruction M hM ((sourceOrder M hM).get i)).source.center 0 := by
  have h := sortBy_get_le (fun b => -centerQ (instruction M hM b).source 0)
    (geometricBranches M hM) hij
  have hq := neg_le_neg_iff.mp h
  have hr : (centerQ (instruction M hM ((sourceOrder M hM).get j)).source 0 : ℝ) ≤
      (centerQ (instruction M hM ((sourceOrder M hM).get i)).source 0 : ℝ) := by
    exact_mod_cast hq
  simpa only [centerQ_cast] using hr

theorem targetOrder_centers (M : Alternating.Machine) (hM : M.WellFormed)
    {i j : Fin (targetOrder M hM).length} (hij : i < j) :
    (instruction M hM ((targetOrder M hM).get i)).target.center 0 ≤
      (instruction M hM ((targetOrder M hM).get j)).target.center 0 := by
  have h := sortBy_get_le (fun b => centerQ (instruction M hM b).target 0)
    (geometricBranches M hM) hij
  have hr : (centerQ (instruction M hM ((targetOrder M hM).get i)).target 0 : ℝ) ≤
      (centerQ (instruction M hM ((targetOrder M hM).get j)).target 0 : ℝ) := by
    exact_mod_cast h
  simpa only [centerQ_cast] using hr

/-- Later source rows do not intersect the active extraction tube. -/
theorem sourceOrder_sweep_gap (M : Alternating.Machine) (hM : M.WellFormed)
    {i j : Fin (sourceOrder M hM).length} (hij : i < j) (endpoint : ℚ) :
    let R := (instruction M hM ((sourceOrder M hM).get i)).source
    let S := (instruction M hM ((sourceOrder M hM).get j)).source
    0 < boxGap R S ∧ EndpointGap (boxGap R S) (rightSweep R endpoint) S := by
  let bi := (sourceOrder M hM).get i
  let bj := (sourceOrder M hM).get j
  have hne : bi ≠ bj := by
    intro he
    exact (ne_of_lt hij) ((List.nodup_iff_injective_get.mp (sourceOrder_nodup M hM)) he)
  have hp := separated_endpointGap (instruction_source_positive M hM bi)
    (instruction_source_positive M hM bj) (instruction_source_separation M hM hne)
  refine ⟨hp.1, rightSweep_gap_of_centers (instruction_source_positive M hM bi)
    (instruction_source_positive M hM bj) hp.1 (sourceOrder_centers M hM hij) hp.2 endpoint⟩

/-- Earlier inserted targets do not intersect the active insertion tube. -/
theorem targetOrder_sweep_gap (M : Alternating.Machine) (hM : M.WellFormed)
    {i j : Fin (targetOrder M hM).length} (hij : i < j) (endpoint : ℚ) :
    let R := (instruction M hM ((targetOrder M hM).get j)).target
    let S := (instruction M hM ((targetOrder M hM).get i)).target
    0 < boxGap R S ∧ EndpointGap (boxGap R S) (rightSweep R endpoint) S := by
  let bi := (targetOrder M hM).get i
  let bj := (targetOrder M hM).get j
  have hne : bj ≠ bi := by
    intro he
    exact (ne_of_lt hij) ((List.nodup_iff_injective_get.mp (targetOrder_nodup M hM)) he.symm)
  have hp := separated_endpointGap (instruction_target_positive M hM bj)
    (instruction_target_positive M hM bi) (instruction_target_separation M hM hne)
  refine ⟨hp.1, rightSweep_gap_of_centers (instruction_target_positive M hM bj)
    (instruction_target_positive M hM bi) hp.1 (targetOrder_centers M hM hij) hp.2 endpoint⟩

end ForcedComputation.Recorder.Planar

end OAI
