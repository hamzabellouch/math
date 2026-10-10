import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryFractionWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Adaptive queries whose answers are stored binary fractions. Local Boolean
computations appear as explicit charged steps. The simulation relation below
preserves the ordered requests as well as the final value; it does not gather
a rational query's keys in advance. -/

namespace EditApproximation



namespace BitQuery



def keys {ι β : Type*} (oracle : ι → BinaryFraction) : BitQuery ι β → List ι
  | .done _ => []
  | .read key next => key :: keys oracle (next (oracle key))
  | .charge _ next => keys oracle next





theorem value_bind {ι α β : Type*} (oracle : ι → BinaryFraction)
    (program : BitQuery ι α) (next : α → BitQuery ι β) :
    (program.bind next).value oracle = (next (program.value oracle)).value oracle := by
  induction program with
  | done result => rfl
  | read key continuation ih => exact ih (oracle key)
  | charge steps continuation ih => exact ih

theorem keys_bind {ι α β : Type*} (oracle : ι → BinaryFraction)
    (program : BitQuery ι α) (next : α → BitQuery ι β) :
    (program.bind next).keys oracle = program.keys oracle ++ (next (program.value oracle)).keys oracle := by
  induction program with
  | done result => rfl
  | read key continuation ih => exact congrArg (List.cons key) (ih (oracle key))
  | charge steps continuation ih => exact ih

theorem work_bind {ι α β : Type*} (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (program : BitQuery ι α) (next : α → BitQuery ι β) :
    (program.bind next).work oracle readWork =
      program.work oracle readWork + (next (program.value oracle)).work oracle readWork := by
  induction program with
  | done result => simp only [bind, work, value, Nat.zero_add]
  | read key continuation ih => simp only [bind, work, value, ih, Nat.add_assoc]
  | charge steps continuation ih => simp only [bind, work, value, ih, Nat.add_assoc]

/- A local charged step executes a Boolean routine with an explicit cost. -/


/-- Branches of the reference query are selected only by the values of
answers actually read. The relation can therefore be composed stage by stage. -/
inductive Refines {ι β : Type*} (relation : β → ℚ → Prop) :
    BitQuery ι β → FiniteQuery ι → Prop where
  | done {result : β} {expected : ℚ} (h : relation result expected) :
      Refines relation (.done result) (.done expected)
  | read (key : ι) (next : BinaryFraction → BitQuery ι β) (expected : ℚ → FiniteQuery ι)
      (h : ∀ word, Refines relation (next word) (expected word.value)) :
      Refines relation (.read key next) (.read key expected)
  | charge (steps : ℕ) {program : BitQuery ι β} {expected : FiniteQuery ι}
      (h : Refines relation program expected) : Refines relation (.charge steps program) expected

theorem Refines.value_keys {ι β : Type*} {relation : β → ℚ → Prop}
    {program : BitQuery ι β} {expected : FiniteQuery ι}
    (h : Refines relation program expected) (oracle : ι → BinaryFraction) :
    relation (program.value oracle) (expected.value (fun key => (oracle key).value)) ∧
      program.keys oracle = expected.keys (fun key => (oracle key).value) := by
  induction h with
  | done h => exact ⟨h, rfl⟩
  | read key next expected h ih =>
    exact ⟨(ih (oracle key)).1, congrArg (List.cons key) (ih (oracle key)).2⟩
  | charge steps h ih => exact ih

theorem Refines.read_work_le {ι β : Type*} {relation : β → ℚ → Prop}
    {program : BitQuery ι β} {expected : FiniteQuery ι}
    (h : Refines relation program expected) (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    expected.cost (fun key => (oracle key).value) readWork ≤ program.work oracle readWork := by
  induction h with
  | done h => exact Nat.le_refl 0
  | read key next expected h ih => exact Nat.add_le_add_left (ih (oracle key)) _
  | charge steps h ih => exact ih.trans (Nat.le_add_left _ _)

theorem Refines.bind {ι α β : Type*} {relation : α → ℚ → Prop}
    {nextRelation : β → ℚ → Prop} {program : BitQuery ι α} {expected : FiniteQuery ι}
    (h : Refines relation program expected) (next : α → BitQuery ι β) (expectedNext : ℚ → FiniteQuery ι)
    (hn : ∀ a v, relation a v → Refines nextRelation (next a) (expectedNext v)) :
    Refines nextRelation (program.bind next) (FiniteQuery.bind expected expectedNext) := by
  induction h with
  | done h => exact hn _ _ h
  | read key continuation expected h ih => exact .read key _ _ ih
  | charge steps h ih => exact .charge steps ih



theorem Refines.collect {ι κ β : Type*} {relation : β → ℚ → Prop}
    (reader : κ → BitQuery ι BinaryFraction) (expectedReader : κ → FiniteQuery ι)
    (hr : ∀ key, Refines (fun word value => word.value = value) (reader key) (expectedReader key))
    (inputs : List κ) (next : List BinaryFraction → BitQuery ι β)
    (expectedNext : List ℚ → FiniteQuery ι)
    (hn : ∀ words, Refines relation (next words) (expectedNext (words.map BinaryFraction.value))) :
    Refines relation (BitQuery.collect reader inputs next)
      (FiniteQuery.collect expectedReader inputs expectedNext) := by
  induction inputs generalizing next expectedNext with
  | nil => exact hn []
  | cons key inputs ih =>
    apply (hr key).bind
    intro word value hv
    subst value
    apply Refines.charge
    apply ih
    intro words
    exact hn (word :: words)

theorem value_collect {ι κ β : Type*} (oracle : ι → BinaryFraction)
    (reader : κ → BitQuery ι BinaryFraction) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) :
    (collect reader inputs next).value oracle =
      (next (inputs.map fun key => (reader key).value oracle)).value oracle := by
  induction inputs generalizing next with
  | nil => rfl
  | cons key inputs ih => simp only [collect, value_bind, value, ih, List.map_cons]

theorem work_collect {ι κ β : Type*} (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (reader : κ → BitQuery ι BinaryFraction) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) :
    (collect reader inputs next).work oracle readWork =
      (inputs.map fun key => (reader key).work oracle readWork + 3).sum +
      (next (inputs.map fun key => (reader key).value oracle)).work oracle readWork := by
  induction inputs generalizing next with
  | nil => simp only [collect, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons key inputs ih =>
    simp only [collect, work_bind, work, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

end BitQuery
end EditApproximation

end OAI
