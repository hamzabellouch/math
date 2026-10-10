import OAI.Combinatorics.EditApproximation.Specification.RawBandPipelineBridges
import OAI.Combinatorics.EditApproximation.Specification.FootprintMain
import OAI.Combinatorics.EditApproximation.Definitions

-- Expose the index expressions inside compiler-generated equality transports.
-- The resulting proof terms are checked by the kernel with the rest of this module.
open Lean Meta Elab Tactic in
elab "unfold_footprint_transports" : tactic => do
  let env ← getEnv
  let names := #[`OAI.EditApproximation.queryChargedFamilyTable,
    `OAI.EditApproximation.queryChargedFamilyTableRawBand,
    `OAI.EditApproximation.queryFamilyBoundedActive,
    `OAI.EditApproximation.queryFamilyBoundedActiveRawBand,
    `OAI.EditApproximation.queryChargedFamilyTableFootprint,
    `OAI.EditApproximation.queryChargedFamilyTableFootprintRawBand]
  let mut goal ← getMainGoal
  for _ in [:16] do
    let target ← goal.getType
    let mut selected : Array Name := #[]
    for n in target.getUsedConstants do
      if let some ci := env.find? n then
        if ci.type.getUsedConstants.any names.contains then
          if ← isProp ci.type then
            selected := selected.push n
    if selected.isEmpty then break
    goal ← goal.change (← deltaExpand target selected.contains (allowOpaque := true)) (checkDefEq := false)
  replaceMainGoal [goal]


namespace OAI.EditApproximation

universe u v

private theorem footprintRanked_congr {κ : Type*} (rank : κ → ℕ)
    (p q : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (hp : p = q) (a : ∀ key, BitQuery.Footprint (p key))
    (b : ∀ key, BitQuery.Footprint (q key)) (hab : HEq a b)
    (bits : ℕ) (encode addressCells : κ → ℕ) (key : κ) (memory : BinaryMemo BinaryFraction) :
    BitQuery.Footprint.rankedBitMemoCells rank p a bits encode addressCells key memory =
      BitQuery.Footprint.rankedBitMemoCells rank q b bits encode addressCells key memory := by
  cases hp
  cases eq_of_heq hab
  rfl

private theorem queryLocalRefinementFootprintRawBand_heq :
    HEq @queryLocalRefinementFootprintRawBand.{u, v} @queryLocalRefinementFootprint.{u, v} := by
  unfold queryLocalRefinementFootprintRawBand queryLocalRefinementFootprint
  unfold queryLocalRefinementRawBand queryLocalRefinement
  rw [BinaryFraction.queryOnlineSelectWithWorkRawBand_eq,
    BinaryFraction.queryGroupSelectWithWorkRawBand_eq]
  simp only [
    BinaryFraction.queryOnlineSelectAllocationRawBand_eq,
    BinaryFraction.queryGroupSelectAllocationRawBand_eq]
  rfl
private theorem queryLocalRandomSourcesFootprintRawBand_heq :
    HEq @queryLocalRandomSourcesFootprintRawBand.{u, v} @queryLocalRandomSourcesFootprint.{u, v} := by
  have hp : @queryLocalRefinementRawBand.{u, v} = @queryLocalRefinement.{u, v} := queryLocalRefinementRawBand_eq
  have hfp : HEq @queryLocalRefinementFootprintRawBand.{u, v} @queryLocalRefinementFootprint.{u, v} := queryLocalRefinementFootprintRawBand_heq
  delta queryLocalRandomSourcesFootprintRawBand queryLocalRandomSourcesFootprint
  delta queryLocalRandomSourcesRawBand queryLocalRandomSources
  generalize hfr : @queryLocalRefinementFootprintRawBand.{u, v} = fr at *
  generalize hfo : @queryLocalRefinementFootprint.{u, v} = fo at *
  clear hfr hfo
  generalize hpr : @queryLocalRefinementRawBand.{u, v} = pr at *
  generalize hpo : @queryLocalRefinement.{u, v} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryLocalBandFootprintRawBand_heq :
    HEq @queryLocalBandFootprintRawBand.{u, v} @queryLocalBandFootprint.{u, v} := by
  have hp : @queryLocalRandomSourcesRawBand.{u, v} = @queryLocalRandomSources.{u, v} := queryLocalRandomSourcesRawBand_eq
  have hfp : HEq @queryLocalRandomSourcesFootprintRawBand.{u, v} @queryLocalRandomSourcesFootprint.{u, v} := queryLocalRandomSourcesFootprintRawBand_heq
  delta queryLocalBandFootprintRawBand queryLocalBandFootprint
  delta queryLocalBandRawBand queryLocalBand
  generalize hfr : @queryLocalRandomSourcesFootprintRawBand.{u, v} = fr at *
  generalize hfo : @queryLocalRandomSourcesFootprint.{u, v} = fo at *
  clear hfr hfo
  generalize hpr : @queryLocalRandomSourcesRawBand.{u, v} = pr at *
  generalize hpo : @queryLocalRandomSources.{u, v} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryLocalProgramFootprintRawBand_heq :
    HEq @queryLocalProgramFootprintRawBand.{u, v} @queryLocalProgramFootprint.{u, v} := by
  have hp : @queryLocalBandRawBand.{u, v} = @queryLocalBand.{u, v} := queryLocalBandRawBand_eq
  have hfp : HEq @queryLocalBandFootprintRawBand.{u, v} @queryLocalBandFootprint.{u, v} := queryLocalBandFootprintRawBand_heq
  delta queryLocalProgramFootprintRawBand queryLocalProgramFootprint
  delta queryLocalProgramRawBand queryLocalProgram
  generalize hfr : @queryLocalBandFootprintRawBand.{u, v} = fr at *
  generalize hfo : @queryLocalBandFootprint.{u, v} = fo at *
  clear hfr hfo
  generalize hpr : @queryLocalBandRawBand.{u, v} = pr at *
  generalize hpo : @queryLocalBand.{u, v} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryPhysicalRandomDataRequestFootprintRawBand_heq :
    HEq @queryPhysicalRandomDataRequestFootprintRawBand.{u, v} @queryPhysicalRandomDataRequestFootprint.{u, v} := by
  have hp : @queryLocalProgramRawBand.{u, v} = @queryLocalProgram.{u, v} := queryLocalProgramRawBand_eq
  have hfp : HEq @queryLocalProgramFootprintRawBand.{u, v} @queryLocalProgramFootprint.{u, v} := queryLocalProgramFootprintRawBand_heq
  delta queryPhysicalRandomDataRequestFootprintRawBand queryPhysicalRandomDataRequestFootprint
  delta queryPhysicalRandomDataRequestRawBand queryPhysicalRandomDataRequest
  generalize hfr : @queryLocalProgramFootprintRawBand.{u, v} = fr at *
  generalize hfo : @queryLocalProgramFootprint.{u, v} = fo at *
  clear hfr hfo
  generalize hpr : @queryLocalProgramRawBand.{u, v} = pr at *
  generalize hpo : @queryLocalProgram.{u, v} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryFamilyRefinementFootprintRawBand_heq :
    HEq @queryFamilyRefinementFootprintRawBand.{u} @queryFamilyRefinementFootprint.{u} := by
  have hp : @queryPhysicalRandomDataRequestRawBand.{0, u} = @queryPhysicalRandomDataRequest.{0, u} := queryPhysicalRandomDataRequestRawBand_eq
  have hfp : HEq @queryPhysicalRandomDataRequestFootprintRawBand.{0, u} @queryPhysicalRandomDataRequestFootprint.{0, u} := queryPhysicalRandomDataRequestFootprintRawBand_heq
  delta queryFamilyRefinementFootprintRawBand queryFamilyRefinementFootprint
  delta queryFamilyRefinementRawBand queryFamilyRefinement
  generalize hfr : @queryPhysicalRandomDataRequestFootprintRawBand.{0, u} = fr at *
  generalize hfo : @queryPhysicalRandomDataRequestFootprint.{0, u} = fo at *
  clear hfr hfo
  generalize hpr : @queryPhysicalRandomDataRequestRawBand.{0, u} = pr at *
  generalize hpo : @queryPhysicalRandomDataRequest.{0, u} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryFamilyActiveFootprintRawBand_heq :
    HEq @queryFamilyActiveFootprintRawBand.{u} @queryFamilyActiveFootprint.{u} := by
  have hp : @queryFamilyRefinementRawBand.{u} = @queryFamilyRefinement.{u} := queryFamilyRefinementRawBand_eq
  have hfp : HEq @queryFamilyRefinementFootprintRawBand.{u} @queryFamilyRefinementFootprint.{u} := queryFamilyRefinementFootprintRawBand_heq
  delta queryFamilyActiveFootprintRawBand queryFamilyActiveFootprint
  delta queryFamilyActiveRawBand queryFamilyActive
  generalize hfr : @queryFamilyRefinementFootprintRawBand.{u} = fr at *
  generalize hfo : @queryFamilyRefinementFootprint.{u} = fo at *
  clear hfr hfo
  generalize hpr : @queryFamilyRefinementRawBand.{u} = pr at *
  generalize hpo : @queryFamilyRefinement.{u} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryFamilyBoundedActiveFootprintRawBand_heq :
    HEq @queryFamilyBoundedActiveFootprintRawBand.{u} @queryFamilyBoundedActiveFootprint.{u} := by
  have hp : @queryFamilyActiveRawBand.{u} = @queryFamilyActive.{u} := queryFamilyActiveRawBand_eq
  have hfp : HEq @queryFamilyActiveFootprintRawBand.{u} @queryFamilyActiveFootprint.{u} := queryFamilyActiveFootprintRawBand_heq
  delta queryFamilyBoundedActiveFootprintRawBand queryFamilyBoundedActiveFootprint
  delta queryFamilyBoundedActiveRawBand queryFamilyBoundedActive
  generalize hfr : @queryFamilyActiveFootprintRawBand.{u} = fr at *
  generalize hfo : @queryFamilyActiveFootprint.{u} = fo at *
  clear hfr hfo
  generalize hpr : @queryFamilyActiveRawBand.{u} = pr at *
  generalize hpo : @queryFamilyActive.{u} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryChargedFamilyTableFootprintRawBand_heq :
    HEq @queryChargedFamilyTableFootprintRawBand @queryChargedFamilyTableFootprint := by
  have hp : @queryFamilyBoundedActiveRawBand.{0} = @queryFamilyBoundedActive.{0} := queryFamilyBoundedActiveRawBand_eq
  have hfp : HEq @queryFamilyBoundedActiveFootprintRawBand.{0} @queryFamilyBoundedActiveFootprint.{0} := queryFamilyBoundedActiveFootprintRawBand_heq
  delta queryChargedFamilyTableFootprintRawBand queryChargedFamilyTableFootprint
  unfold_footprint_transports
  delta queryChargedFamilyTableRawBand queryChargedFamilyTable
  generalize hfr : @queryFamilyBoundedActiveFootprintRawBand.{0} = fr at *
  generalize hfo : @queryFamilyBoundedActiveFootprint.{0} = fo at *
  clear hfr hfo
  generalize hpr : @queryFamilyBoundedActiveRawBand.{0} = pr at *
  generalize hpo : @queryFamilyBoundedActive.{0} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryChargedFamilyGlobalFootprintRawBand_heq :
    HEq @queryChargedFamilyGlobalFootprintRawBand @queryChargedFamilyGlobalFootprint := by
  have hp : @queryChargedFamilyTableRawBand = @queryChargedFamilyTable := queryChargedFamilyTableRawBand_eq
  have hfp : HEq @queryChargedFamilyTableFootprintRawBand @queryChargedFamilyTableFootprint := queryChargedFamilyTableFootprintRawBand_heq
  delta queryChargedFamilyGlobalFootprintRawBand queryChargedFamilyGlobalFootprint
  delta queryChargedFamilyGlobalRawBand queryChargedFamilyGlobal
  generalize hfr : @queryChargedFamilyTableFootprintRawBand = fr at *
  generalize hfo : @queryChargedFamilyTableFootprint = fo at *
  clear hfr hfo
  generalize hpr : @queryChargedFamilyTableRawBand = pr at *
  generalize hpo : @queryChargedFamilyTable = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryFamilyMemoRawFootprintRawBand_heq :
    HEq @queryFamilyMemoRawFootprintRawBand @queryFamilyMemoRawFootprint := by
  have hp : @queryChargedFamilyGlobalRawBand = @queryChargedFamilyGlobal := queryChargedFamilyGlobalRawBand_eq
  have hfp : HEq @queryChargedFamilyGlobalFootprintRawBand @queryChargedFamilyGlobalFootprint := queryChargedFamilyGlobalFootprintRawBand_heq
  delta queryFamilyMemoRawFootprintRawBand queryFamilyMemoRawFootprint
  delta queryFamilyMemoRawRawBand queryFamilyMemoRaw
  generalize hfr : @queryChargedFamilyGlobalFootprintRawBand = fr at *
  generalize hfo : @queryChargedFamilyGlobalFootprint = fo at *
  clear hfr hfo
  generalize hpr : @queryChargedFamilyGlobalRawBand = pr at *
  generalize hpo : @queryChargedFamilyGlobal = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem computedQueryMemoRawFootprintRawBand_heq :
    HEq @computedQueryMemoRawFootprintRawBand @computedQueryMemoRawFootprint := by
  have hp : @queryFamilyMemoRawRawBand = @queryFamilyMemoRaw := queryFamilyMemoRawRawBand_eq
  have hfp : HEq @queryFamilyMemoRawFootprintRawBand @queryFamilyMemoRawFootprint := queryFamilyMemoRawFootprintRawBand_heq
  delta computedQueryMemoRawFootprintRawBand computedQueryMemoRawFootprint
  delta computedQueryMemoRawRawBand computedQueryMemoRaw
  generalize hfr : @queryFamilyMemoRawFootprintRawBand = fr at *
  generalize hfo : @queryFamilyMemoRawFootprint = fo at *
  clear hfr hfo
  generalize hpr : @queryFamilyMemoRawRawBand = pr at *
  generalize hpo : @queryFamilyMemoRaw = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

theorem computedQueryMemoFootprintRawBand_heq (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) :
    HEq (computedQueryMemoFootprintRawBand source target N occurrence symbolBits positionBits input)
      (computedQueryMemoFootprint source target N occurrence symbolBits positionBits input) := by
  have hp : @computedQueryMemoRawRawBand = @computedQueryMemoRaw := computedQueryMemoRawRawBand_eq
  have hfp : HEq @computedQueryMemoRawFootprintRawBand @computedQueryMemoRawFootprint := computedQueryMemoRawFootprintRawBand_heq
  delta computedQueryMemoFootprintRawBand computedQueryMemoFootprint
  delta computedQueryMemoNormalizedRawBand computedQueryMemoNormalized
  generalize hfr : @computedQueryMemoRawFootprintRawBand = fr at *
  generalize hfo : @computedQueryMemoRawFootprint = fo at *
  clear hfr hfo
  generalize hpr : @computedQueryMemoRawRawBand = pr at *
  generalize hpo : @computedQueryMemoRaw = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

theorem computedQueryTemporaryCellsFootprintRawBand_eq (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedQueryTemporaryCellsFootprintRawBand source target N occurrence symbolBits positionBits input =
      computedQueryTemporaryCellsFootprint source target N occurrence symbolBits positionBits input := by
  unfold computedQueryTemporaryCellsFootprintRawBand computedQueryTemporaryCellsFootprint
  apply footprintRanked_congr
  · rw [computedQueryMemoNormalizedRawBand_eq]
  · exact computedQueryMemoFootprintRawBand_heq source target N occurrence symbolBits positionBits input

theorem integerAcceptedSpaceTermsFootprintRawBand_eq (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerAcceptedSpaceTermsFootprintRawBand source target N epsilon input =
      integerAcceptedSpaceTermsFootprint source target N epsilon input := by
  simp only [integerAcceptedSpaceTermsFootprintRawBand, integerAcceptedSpaceTermsFootprint,
    computedQueryTemporaryCellsFootprintRawBand_eq, computedQueryMemoResultRawBand_eq,
    integerFinalAllocationRawBand_eq]

theorem integerBinarySpaceFootprintRawBand_eq (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerBinarySpaceFootprintRawBand source target N epsilon outcome =
      integerBinarySpaceFootprint source target N epsilon outcome := by
  simp only [integerBinarySpaceFootprintRawBand, integerBinarySpaceFootprint,
    integerAcceptedSpaceTermsFootprintRawBand_eq]
  rfl

end OAI.EditApproximation
