import OAI.Combinatorics.EditApproximation.Binary.BinaryMemo

namespace OAI

/-! One local calculation gathers its distinct recursive inputs once.
Subsequent scoring and optimizer iterations use the binary dictionary.
The counters record oracle calls and actual persistent node writes. -/

namespace EditApproximation

structure GatheredInputs where
  memory : BinaryMemo ℚ
  recursiveCalls : ℕ
  nodeWrites : ℕ

def gatherInputs {ι : Type*} (bits : ℕ) (encode : ι → ℕ) (fetch : ι → ℚ) :
    List ι → GatheredInputs
  | [] => ⟨.empty, 0, 0⟩
  | input :: rest =>
    let previous := gatherInputs bits encode fetch rest
    let added := previous.memory.insertCosted (binaryMemoKey bits (encode input)) (fetch input)
    ⟨added.1, previous.recursiveCalls + 1, previous.nodeWrites + added.2⟩

theorem gatherInputs_calls {ι : Type*} (bits : ℕ) (encode : ι → ℕ) (fetch : ι → ℚ)
    (inputs : List ι) : (gatherInputs bits encode fetch inputs).recursiveCalls = inputs.length := by
  induction inputs with
  | nil => rfl
  | cons input rest ih => simpa only [gatherInputs, List.length_cons] using congrArg (· + 1) ih

theorem gatherInputs_writes {ι : Type*} (bits : ℕ) (encode : ι → ℕ) (fetch : ι → ℚ)
    (inputs : List ι) :
    (gatherInputs bits encode fetch inputs).nodeWrites = inputs.length * (bits + 1) := by
  induction inputs with
  | nil => simp only [gatherInputs, List.length_nil, Nat.zero_mul]
  | cons input rest ih =>
    simp only [gatherInputs, BinaryMemo.insertCosted_spec, binaryMemoKey_length, ih,
      List.length_cons, Nat.add_mul, Nat.one_mul]

theorem gatherInputs_lookup {ι : Type*} (bits : ℕ) (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (fetch : ι → ℚ) (inputs : List ι)
    (hbounded : ∀ input ∈ inputs, encode input < 2 ^ bits)
    (query : ι) (hquery : query ∈ inputs) :
    (gatherInputs bits encode fetch inputs).memory.lookup (binaryMemoKey bits (encode query)) =
      some (fetch query) := by
  induction inputs with
  | nil => simp only [List.not_mem_nil] at hquery
  | cons input rest ih =>
    simp only [gatherInputs, BinaryMemo.insertCosted_spec]
    rw [binaryMemo_lookup_insert _ bits (encode input) (encode query)
      (hbounded input (List.mem_cons_self)) (hbounded query hquery)]
    by_cases heq : query = input
    · subst query
      simp only [ite_true]
    · rw [ite_eq_right (fun h => heq (hinjective h))]
      exact ih (fun other hother => hbounded other (List.mem_cons_of_mem _ hother))
        (List.mem_of_ne_of_mem heq hquery)

theorem gatherInputs_nodes {ι : Type*} (bits : ℕ) (encode : ι → ℕ) (fetch : ι → ℚ)
    (inputs : List ι) :
    (gatherInputs bits encode fetch inputs).memory.nodes ≤ inputs.length * (bits + 1) := by
  induction inputs with
  | nil => exact Nat.zero_le _
  | cons input rest ih =>
    simp only [gatherInputs, BinaryMemo.insertCosted_spec]
    have h := BinaryMemo.insert_nodes (gatherInputs bits encode fetch rest).memory
      (binaryMemoKey bits (encode input)) (fetch input)
    simp only [binaryMemoKey_length] at h
    calc
      _ ≤ (gatherInputs bits encode fetch rest).memory.nodes + bits + 1 := h
      _ ≤ rest.length * (bits + 1) + bits + 1 := Nat.add_le_add_right (Nat.add_le_add_right ih _) _
      _ = (input :: rest).length * (bits + 1) := by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega

end EditApproximation

end OAI
