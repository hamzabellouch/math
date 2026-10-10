import OAI.Combinatorics.EditApproximation.Geometry.LocalWideStep
import OAI.Combinatorics.EditApproximation.Geometry.GatheredInputs
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The current-index part of a local step can be evaluated in two
stages: gather the shared sampled inputs, select the whole-cell actions,
then gather their actual costs and the online action costs. -/

namespace EditApproximation

open Finset

theorem localCellGroupActions_congr_cover {α : Type*}
    (source target : List α) {M : ℕ} (parent : TargetInterval source.length)
    (N P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current current' : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (hvalue : ∀ input ∈ querySharedInputCover source target parent N F exponent Q a parentInitial q draw,
      current input.1 input.2 = current' input.1 input.2) :
    localCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw q =
      localCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current' draw q := by
  unfold localCellGroupActions
  apply List.flatMap_congr
  intro b hb
  apply List.filterMap_congr
  intro cell hc
  have hscale : b ∈ dyadicScales N := (List.mem_filter.mp hb).1
  have hbpos : 1 ≤ b := by
    obtain ⟨e, _, he⟩ := List.mem_map.mp hscale
    rw [← he]
    exact Nat.one_le_two_pow
  apply chooseCellGroupAction_congr_cover source target parent tau a F Q parentInitial
    child initial current current' cell hbpos (draw b cell)
  intro scale input hi
  apply hvalue input
  apply Finset.mem_biUnion.mpr
  refine ⟨(b, cell), ?_, Finset.mem_biUnion.mpr ⟨scale, Finset.mem_univ _, hi⟩⟩
  apply List.mem_toFinset.mpr
  exact List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨cell, hc, rfl⟩⟩

theorem rationalActionValues_congr_cover {Parent Child : Type*} [DecidableEq Child] {M : ℕ}
    (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (RationalBellmanAction Parent Child M)) (q : Parent)
    (value value' : Child → ℚ)
    (hvalue : ∀ input ∈ actionCurrentInputCover actions, value input = value' input) :
    actions.map (rationalActionValue distance L value q) =
      actions.map (rationalActionValue distance L value' q) := by
  apply List.map_congr_left
  intro action ha
  unfold rationalActionValue
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hvalue _ (actionCurrentInputCover_mem actions action ha i)

def gatheredInputValue {ι : Type*} (bits : ℕ) (encode : ι → ℕ) (fetch : ι → ℚ)
    (inputs : List ι) (input : ι) : ℚ :=
  ((gatherInputs bits encode fetch inputs).memory.lookup (binaryMemoKey bits (encode input))).getD 0

theorem gatheredInputValue_eq {ι : Type*} (bits : ℕ) (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (fetch : ι → ℚ) (inputs : List ι)
    (hbounded : ∀ input ∈ inputs, encode input < 2 ^ bits)
    (input : ι) (hinput : input ∈ inputs) :
    gatheredInputValue bits encode fetch inputs input = fetch input := by
  unfold gatheredInputValue
  rw [gatherInputs_lookup bits encode hinjective fetch inputs hbounded input hinput]
  rfl



theorem mem_orderedInputs {ι : Type*} [DecidableEq ι] (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (inputs : Finset ι) (input : ι) :
    input ∈ orderedInputs encode hinjective inputs ↔ input ∈ inputs := by
  let _ : LinearOrder ι := LinearOrder.lift' encode hinjective
  exact Finset.mem_sort (r := (· ≤ ·))

theorem orderedInputs_length {ι : Type*} [DecidableEq ι] (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (inputs : Finset ι) :
    (orderedInputs encode hinjective inputs).length = inputs.card := by
  let _ : LinearOrder ι := LinearOrder.lift' encode hinjective
  exact Finset.length_sort (r := (· ≤ ·))

def gatheredFiniteValue {ι : Type*} [DecidableEq ι] (bits : ℕ) (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (fetch : ι → ℚ) (inputs : Finset ι) : ι → ℚ :=
  gatheredInputValue bits encode fetch (orderedInputs encode hinjective inputs)

theorem gatheredFiniteValue_eq {ι : Type*} [DecidableEq ι] (bits : ℕ) (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (fetch : ι → ℚ) (inputs : Finset ι)
    (hbounded : ∀ input, encode input < 2 ^ bits) (input : ι) (hinput : input ∈ inputs) :
    gatheredFiniteValue bits encode hinjective fetch inputs input = fetch input :=
  gatheredInputValue_eq bits encode hinjective fetch _ (fun i _ => hbounded i) input
    ((mem_orderedInputs encode hinjective inputs input).2 hinput)

section TwoStage

variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a delta : ℚ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial old current : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q) (online : List (PhysicalRationalAction M target.length))
  (q : TargetInterval target.length) (bits : ℕ)
  (encode : Fin M × TargetInterval target.length → ℕ) (hinjective : Function.Injective encode)

local notation "shared" => querySharedInputCover source target parent N F exponent Q a parentInitial q draw
local notation "groups" => localCellGroupActions source target parent N P F exponent Q tau a parentInitial
  child initial current draw q

def gatheredCellGroupActions : List (PhysicalRationalAction M target.length) :=
  let cached := gatheredFiniteValue bits encode hinjective (fun input => current input.1 input.2) shared
  localCellGroupActions source target parent N P F exponent Q tau a parentInitial
    child initial (fun i r => cached (i, r)) draw q

theorem gatheredCellGroupActions_eq (hbounded : ∀ input, encode input < 2 ^ bits) :
    gatheredCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q bits encode hinjective = groups := by
  apply localCellGroupActions_congr_cover
  intro input hinput
  exact gatheredFiniteValue_eq bits encode hinjective _ shared hbounded input hinput

def gatheredLocalWideStep : ℚ :=
  let selected := gatheredCellGroupActions source target parent N P F exponent Q tau a parentInitial
    child initial current draw q bits encode hinjective
  let needed := actionCurrentInputCover selected ∪ actionCurrentInputCover online
  let cached := gatheredFiniteValue bits encode hinjective (fun input => current input.1 input.2) needed
  let value := rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F) cached q
  let fallback := rationalBellman parentInitial (fun q r => targetEndpointDistance q r) (128 * F)
    (rationalActualWideActions parent (localRefinementRepresentatives N P F a parentInitial q) P)
    (fun input => old input.1 input.2) q
  rationalRefinementUpdate delta (rationalMinimum fallback (selected.map value))
    (rationalOnlineMinimum (online.map value))

theorem gatheredLocalWideStep_eq (hbounded : ∀ input, encode input < 2 ^ bits) :
    gatheredLocalWideStep source target parent N P F exponent Q tau a delta parentInitial
      child initial old current draw online q bits encode hinjective =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial
      child initial old current draw online q := by
  unfold gatheredLocalWideStep
  rw [gatheredCellGroupActions_eq source target parent N P F exponent Q tau a parentInitial
    child initial current draw q bits encode hinjective hbounded]
  dsimp only
  let needed := actionCurrentInputCover groups ∪ actionCurrentInputCover online
  have hgroup := rationalActionValues_congr_cover
    (fun q r : TargetInterval target.length => (targetEndpointDistance q r : ℚ)) (128 * F) groups q
    (gatheredFiniteValue bits encode hinjective (fun input => current input.1 input.2) needed)
    (fun input => current input.1 input.2)
    (fun input hi => gatheredFiniteValue_eq bits encode hinjective _ needed hbounded input
      (Finset.mem_union_left _ hi))
  have honline := rationalActionValues_congr_cover
    (fun q r : TargetInterval target.length => (targetEndpointDistance q r : ℚ)) (128 * F) online q
    (gatheredFiniteValue bits encode hinjective (fun input => current input.1 input.2) needed)
    (fun input => current input.1 input.2)
    (fun input hi => gatheredFiniteValue_eq bits encode hinjective _ needed hbounded input
      (Finset.mem_union_right _ hi))
  rw [hgroup, honline]
  rfl

/-- Actual oracle requests in the two gathers. Each list is sorted and
contains no duplicates; overlap between the two stages is harmless. -/
def gatheredLocalCurrentCalls : ℕ :=
  (gatherInputs bits encode (fun input => current input.1 input.2)
    (orderedInputs encode hinjective shared)).recursiveCalls +
  (gatherInputs bits encode (fun input => current input.1 input.2)
    (orderedInputs encode hinjective
      (actionCurrentInputCover
        (gatheredCellGroupActions source target parent N P F exponent Q tau a parentInitial
          child initial current draw q bits encode hinjective) ∪ actionCurrentInputCover online))).recursiveCalls

theorem gatheredLocalCurrentCalls_le (hbounded : ∀ input, encode input < 2 ^ bits) :
    gatheredLocalCurrentCalls source target parent N P F exponent Q tau a parentInitial
      child initial current draw online q bits encode hinjective ≤
    2 * (currentQueryInputCover source target parent N P F exponent Q tau a parentInitial
      child initial current draw q online).card := by
  unfold gatheredLocalCurrentCalls
  rw [gatherInputs_calls, gatherInputs_calls, orderedInputs_length, orderedInputs_length,
    gatheredCellGroupActions_eq source target parent N P F exponent Q tau a parentInitial
      child initial current draw q bits encode hinjective hbounded]
  have hshared : (shared).card ≤ (currentQueryInputCover source target parent N P F exponent Q tau a
      parentInitial child initial current draw q online).card := Finset.card_le_card (by
    intro input hi
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hi))
  have hselected : (actionCurrentInputCover groups ∪ actionCurrentInputCover online).card ≤
      (currentQueryInputCover source target parent N P F exponent Q tau a
        parentInitial child initial current draw q online).card := Finset.card_le_card (by
    intro input hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
    · exact Finset.mem_union_right _ hi)
  omega

end TwoStage

end EditApproximation

end OAI
