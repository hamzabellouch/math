import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryRestriction
import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoSimulation

namespace OAI

/-! Restrict a well-founded query program to its proved finite key domain.
Values, executed read lists and weighted read costs are preserved. -/

namespace EditApproximation

 def restrictRankedProgram {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (P : κ → Prop) [DecidablePred P] (key : {key // P key}) :
    FiniteQuery {child : {key // P key} // rank child.val < rank key.val} :=
  FiniteQuery.mapKeys (fun child => ⟨⟨child.val.val, child.property⟩, child.val.property⟩)
    (FiniteQuery.restrict (fun child => P child.val) (program key.val))

 theorem restrictRankedProgram_value {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (P : κ → Prop) [DecidablePred P] (expected : κ → ℚ) (key : {key // P key})
    (hvalid : ∀ child ∈ (program key.val).keys (fun child => expected child.val), P child.val) :
    (restrictRankedProgram rank program P key).value (fun child => expected child.val.val) =
      (program key.val).value (fun child => expected child.val) := by
  unfold restrictRankedProgram
  rw [FiniteQuery.mapKeys_value]
  exact FiniteQuery.restrict_value _ _ _ hvalid

 theorem restrictRankedProgram_cost {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (P : κ → Prop) [DecidablePred P] (expected : κ → ℚ) (weight : κ → ℕ) (key : {key // P key})
    (hvalid : ∀ child ∈ (program key.val).keys (fun child => expected child.val), P child.val) :
    (restrictRankedProgram rank program P key).cost
        (fun child => expected child.val.val) (fun child => weight child.val.val) =
      (program key.val).cost (fun child => expected child.val) (fun child => weight child.val) := by
  unfold restrictRankedProgram
  rw [FiniteQuery.mapKeys_cost]
  simpa only [Function.comp_def] using
    (FiniteQuery.restrict_cost (fun child => P child.val) (fun child => expected child.val)
      (fun child => weight child.val) (program key.val) hvalid)

 theorem restrictRankedProgram_keys {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (P : κ → Prop) [DecidablePred P] (expected : κ → ℚ) (key : {key // P key})
    (hvalid : ∀ child ∈ (program key.val).keys (fun child => expected child.val), P child.val) :
    ((restrictRankedProgram rank program P key).keys
      (fun child => expected child.val.val)).map (fun child => child.val.val) =
      ((program key.val).keys (fun child => expected child.val)).map Subtype.val := by
  unfold restrictRankedProgram
  rw [FiniteQuery.mapKeys_keys, List.map_map]
  have hkeys := FiniteQuery.restrict_keys (fun child => P child.val)
    (fun child => expected child.val) (program key.val) hvalid
  have hmap := congrArg (List.map Subtype.val) hkeys
  simpa only [List.map_map, Function.comp_def] using hmap

 theorem restrictRankedProgram_specification {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (P : κ → Prop) [DecidablePred P] (expected : κ → ℚ)
    (hstep : ∀ key, P key → (program key).value (fun child => expected child.val) = expected key)
    (hvalid : ∀ key, P key → ∀ child ∈ (program key).keys (fun child => expected child.val), P child.val)
    (key : {key // P key}) :
    rankedProgramValue (fun key : {key // P key} => rank key.val)
      (restrictRankedProgram rank program P) key = expected key.val := by
  refine rankedProgramValue_eq (fun key : {key // P key} => rank key.val)
    (restrictRankedProgram rank program P) (fun key : {key // P key} => expected key.val) ?_ key
  intro other
  rw [restrictRankedProgram_value rank program P expected other (hvalid other.val other.property)]
  exact hstep other.val other.property

end EditApproximation

end OAI
