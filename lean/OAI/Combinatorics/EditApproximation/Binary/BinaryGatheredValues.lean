import OAI.Combinatorics.EditApproximation.Refinement.PhysicalBinaryMass
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandCoordinates
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmupQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Finite stored-word tables for gathered earlier values. The lookup scan
and the construction of every gathered warmup mean are explicit. -/

namespace EditApproximation
namespace BinaryFraction



theorem gatheredWordLookupWithWork_value {κ : Type*} [DecidableEq κ]
    (equal : κ → κ → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (keys : List κ) (values : List BinaryFraction) (query : κ) :
    (gatheredWordLookupWithWork equal keys values query).1.value =
      finiteAnswerTable keys (values.map BinaryFraction.value) query := by
  induction keys generalizing values with
  | nil => simp only [gatheredWordLookupWithWork, finiteAnswerTable, nat_value, Nat.cast_zero]
  | cons key keys ih =>
    cases values with
    | nil => simp only [gatheredWordLookupWithWork, List.map_nil, finiteAnswerTable, nat_value, Nat.cast_zero]
    | cons value values =>
      simp only [gatheredWordLookupWithWork, List.map_cons, finiteAnswerTable]
      by_cases h : query = key
      · rw [ite_eq_left ((heq query key).mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hx => h ((heq query key).mp hx)), ite_eq_right h]
        exact ih values

theorem gatheredWordLookupWithWork_cost {κ : Type*}
    (equal : κ → κ → Bool × ℕ) (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C)
    (keys : List κ) (values : List BinaryFraction) (query : κ) :
    (gatheredWordLookupWithWork equal keys values query).2 ≤ 1 + keys.length * (C + 1) := by
  induction keys generalizing values with
  | nil => simp only [gatheredWordLookupWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_rfl]
  | cons key keys ih =>
    cases values with
    | nil => simp only [gatheredWordLookupWithWork]; omega
    | cons value values =>
      have hc := hC query key
      have hi := ih values
      simp only [gatheredWordLookupWithWork]
      split_ifs <;> simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega

theorem gatheredWordLookupWithWork_width {κ : Type*}
    (equal : κ → κ → Bool × ℕ) (keys : List κ) (values : List BinaryFraction) (query : κ)
    (B : ℕ) (hB : 2 ≤ B) (hvalues : ∀ value ∈ values, value.width ≤ B) :
    (gatheredWordLookupWithWork equal keys values query).1.width ≤ B := by
  induction keys generalizing values with
  | nil => exact (nat_width_le 0).trans (by simpa using hB)
  | cons key keys ih =>
    cases values with
    | nil => exact (nat_width_le 0).trans (by simpa using hB)
    | cons value values =>
      simp only [gatheredWordLookupWithWork]
      split_ifs
      · exact hvalues value List.mem_cons_self
      · exact ih values (fun v hv => hvalues v (List.mem_cons_of_mem _ hv))

def gatheredMassWordsWithWork {ny M : ℕ} (T : ℕ)
    (words : Fin M → ℕ → TargetInterval ny → BinaryFraction)
    (inputs : List (Fin M × TargetInterval ny)) : List BinaryFraction × ℕ :=
  arithmeticMapWithWork (fun input => physicalWarmupMassWithWork T (words input.1) input.2) inputs

@[simp] theorem gatheredMassWordsWithWork_value {ny M : ℕ} (T : ℕ)
    (words : Fin M → ℕ → TargetInterval ny → BinaryFraction)
    (inputs : List (Fin M × TargetInterval ny)) :
    (gatheredMassWordsWithWork T words inputs).1 =
      inputs.map (fun input => (physicalWarmupMassWithWork T (words input.1) input.2).1) :=
  arithmeticMapWithWork_value _ _

theorem gatheredMassWordsWithWork_bounds {ny M : ℕ} (T B : ℕ)
    (words : Fin M → ℕ → TargetInterval ny → BinaryFraction)
    (inputs : List (Fin M × TargetInterval ny))
    (hwords : ∀ i j, j < T → ∀ r, (words i j r).width ≤ B) :
    (gatheredMassWordsWithWork T words inputs).2 ≤
      1 + inputs.length * (warmupAverageBitBudget T B + T + 4) ∧
    ∀ value ∈ (gatheredMassWordsWithWork T words inputs).1,
      value.width ≤ warmupAverageWordBudget T B := by
  constructor
  · have h := arithmeticMapWithWork_cost
      (fun input : Fin M × TargetInterval ny => physicalWarmupMassWithWork T (words input.1) input.2)
      inputs (warmupAverageBitBudget T B + T + 1) (by
        intro input _
        exact (physicalWarmupMassWithWork_bounds T B (words input.1)
          (fun j hj r => hwords input.1 j hj r) input.2).2)
    simpa only [gatheredMassWordsWithWork, Nat.add_assoc, Nat.reduceAdd] using h.trans (Nat.le_add_left _ 1)
  · intro value hv
    rw [gatheredMassWordsWithWork_value] at hv
    obtain ⟨input, _, rfl⟩ := List.mem_map.mp hv
    exact (physicalWarmupMassWithWork_bounds T B (words input.1)
      (fun j hj r => hwords input.1 j hj r) input.2).1

theorem gatheredMassLookup_value {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F T : ℕ) (A : ℚ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (words : Fin M → ℕ → TargetInterval target.length → BinaryFraction)
    (inputs : List (Fin M × TargetInterval target.length))
    (hwords : ∀ i j, j < T → ∀ r, (words i j r).value =
      physicalLocalWarmup source target U N P F A j (physicalChild node hbelow i, r))
    (query : Fin M × TargetInterval target.length) (hquery : query ∈ inputs) :
    (gatheredWordLookupWithWork coordinateEqualWithWork inputs
      (gatheredMassWordsWithWork T words inputs).1 query).1.value =
      physicalLocalChildMass source target U N P F A T node hbelow query.1 query.2 := by
  rw [gatheredWordLookupWithWork_value _ coordinateEqualWithWork_value,
    gatheredMassWordsWithWork_value, List.map_map]
  rw [finiteAnswerTable_map _ _ query hquery]
  exact physicalWarmupMassWithWork_value source target U N P F T A
    (physicalChild node hbelow query.1) (words query.1) (hwords query.1) query.2


def gatheredWordBits (values : List BinaryFraction) : ℕ :=
  (values.map fun value => value.width + 1).sum

theorem gatheredWordBits_le (values : List BinaryFraction) (B : ℕ)
    (hb : ∀ value ∈ values, value.width ≤ B) :
    gatheredWordBits values ≤ values.length * (B + 1) := by
  induction values with
  | nil => simp only [gatheredWordBits, List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons value values ih =>
    have hhead := hb value List.mem_cons_self
    have htail := ih (fun v hv => hb v (List.mem_cons_of_mem _ hv))
    simp only [gatheredWordBits, List.map_cons, List.sum_cons, List.length_cons,
      Nat.add_mul, Nat.one_mul] at *
    omega

theorem gatheredMassWordsWithWork_storage {ny M : ℕ} (T B : ℕ)
    (words : Fin M → ℕ → TargetInterval ny → BinaryFraction)
    (inputs : List (Fin M × TargetInterval ny))
    (hwords : ∀ i j, j < T → ∀ r, (words i j r).width ≤ B) :
    gatheredWordBits (gatheredMassWordsWithWork T words inputs).1 ≤
      inputs.length * (warmupAverageWordBudget T B + 1) := by
  have h := gatheredWordBits_le (gatheredMassWordsWithWork T words inputs).1
    (warmupAverageWordBudget T B) (gatheredMassWordsWithWork_bounds T B words inputs hwords).2
  simpa only [gatheredMassWordsWithWork_value, List.length_map] using h

end BinaryFraction
end EditApproximation

end OAI
