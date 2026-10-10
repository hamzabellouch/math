import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Restriction of adaptive read programs to a proved finite request domain.
The restriction visits the same reads whenever the original execution stays
in that domain. It does not enumerate the domain. -/

namespace EditApproximation.FiniteQuery



 theorem mapKeys_id {ι : Type*} (program : FiniteQuery ι) : mapKeys id program = program := by
  induction program with
  | done result => rfl
  | read key next ih =>
    simp only [mapKeys, id_eq]
    congr
    funext answer
    exact ih answer


 theorem mapKeys_value {ι κ : Type*} (f : ι → κ) (oracle : κ → ℚ) (program : FiniteQuery ι) :
    (mapKeys f program).value oracle = program.value (oracle ∘ f) := by
  induction program with
  | done result => rfl
  | read key next ih => exact ih (oracle (f key))

 theorem mapKeys_cost {ι κ : Type*} (f : ι → κ) (oracle : κ → ℚ) (weight : κ → ℕ)
    (program : FiniteQuery ι) :
    (mapKeys f program).cost oracle weight = program.cost (oracle ∘ f) (weight ∘ f) := by
  induction program with
  | done result => rfl
  | read key next ih => exact congrArg (fun rest => weight (f key) + rest) (ih (oracle (f key)))

 theorem mapKeys_keys {ι κ : Type*} (f : ι → κ) (oracle : κ → ℚ) (program : FiniteQuery ι) :
    (mapKeys f program).keys oracle = (program.keys (oracle ∘ f)).map f := by
  induction program with
  | done result => rfl
  | read key next ih => exact congrArg (List.cons (f key)) (ih (oracle (f key)))



 theorem restrict_value {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (oracle : ι → ℚ) (program : FiniteQuery ι)
    (hvalid : ∀ key ∈ program.keys oracle, P key) :
    (restrict P program).value (fun key => oracle key.val) = program.value oracle := by
  induction program with
  | done result => rfl
  | read key next ih =>
    have hk : P key := hvalid key (by simp only [keys, List.mem_cons, true_or])
    have hnext : ∀ other ∈ (next (oracle key)).keys oracle, P other := by
      intro other hother
      exact hvalid other (List.mem_cons_of_mem key hother)
    simpa only [restrict, dite_eq_left hk, value] using ih (oracle key) hnext

 theorem restrict_cost {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (oracle : ι → ℚ) (weight : ι → ℕ) (program : FiniteQuery ι)
    (hvalid : ∀ key ∈ program.keys oracle, P key) :
    (restrict P program).cost (fun key => oracle key.val) (fun key => weight key.val) =
      program.cost oracle weight := by
  induction program with
  | done result => rfl
  | read key next ih =>
    have hk : P key := hvalid key (by simp only [keys, List.mem_cons, true_or])
    have hnext : ∀ other ∈ (next (oracle key)).keys oracle, P other := by
      intro other hother
      exact hvalid other (List.mem_cons_of_mem key hother)
    simpa only [restrict, dite_eq_left hk, cost] using
      congrArg (fun rest => weight key + rest) (ih (oracle key) hnext)

 theorem restrict_keys {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (oracle : ι → ℚ) (program : FiniteQuery ι)
    (hvalid : ∀ key ∈ program.keys oracle, P key) :
    ((restrict P program).keys (fun key => oracle key.val)).map Subtype.val = program.keys oracle := by
  induction program with
  | done result => rfl
  | read key next ih =>
    have hk : P key := hvalid key (by simp only [keys, List.mem_cons, true_or])
    have hnext : ∀ other ∈ (next (oracle key)).keys oracle, P other := by
      intro other hother
      exact hvalid other (List.mem_cons_of_mem key hother)
    simpa only [restrict, dite_eq_left hk, keys, List.map_cons] using
      congrArg (List.cons key) (ih (oracle key) hnext)

end EditApproximation.FiniteQuery

end OAI
