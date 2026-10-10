import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoProgram

namespace OAI

/-! Counts of the actual persistent interpreter. Dictionary operations
are charged on every request, including hits; insertion and retained-node
costs are charged only when a value is computed. -/

namespace EditApproximation

namespace FiniteQuery

def cost {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ) : FiniteQuery ι → ℕ
  | .done _ => 0
  | .read key next => weight key + cost oracle weight (next (oracle key))

def keys {ι : Type*} (oracle : ι → ℚ) : FiniteQuery ι → List ι
  | .done _ => []
  | .read key next => key :: keys oracle (next (oracle key))

theorem cost_eq_sum {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) :
    program.cost oracle weight = ((program.keys oracle).map weight).sum := by
  induction program with
  | done _ => rfl
  | read key next ih => exact congrArg (weight key + ·) (ih (oracle key))

theorem run_resource_bounds {ι κ : Type*}
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ) (B D : ℕ)
    (hask : ∀ key memory,
      (ask key memory).freshKeys.length ≤ (ask key memory).requests ∧
      (ask key memory).dictionaryVisits ≤ (ask key memory).requests * D ∧
      (ask key memory).memory.nodes ≤ memory.nodes + (ask key memory).freshKeys.length * B)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ) :
    (run ask program memory).freshKeys.length ≤ (run ask program memory).requests ∧
    (run ask program memory).dictionaryVisits ≤ (run ask program memory).requests * D ∧
    (run ask program memory).memory.nodes ≤ memory.nodes + (run ask program memory).freshKeys.length * B := by
  induction program generalizing memory with
  | done _ => simp only [run, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl, and_self]
  | read key next ih =>
    have hf := hask key memory
    have hr := ih (ask key memory).value (ask key memory).memory
    dsimp only [run]
    simp only [List.length_append, Nat.add_mul]
    exact ⟨Nat.add_le_add hf.1 hr.1, Nat.add_le_add hf.2.1 hr.2.1, by omega⟩

theorem run_requests_le {ι κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → ℚ) (answer : ι → ℚ) (weight : ι → ℕ)
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, memoSound bits encode expected memory →
      (ask key memory).value = answer key ∧
      memoSound bits encode expected (ask key memory).memory ∧
      (ask key memory).requests ≤ weight key)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode expected memory) :
    (run ask program memory).requests ≤ program.cost answer weight := by
  induction program generalizing memory with
  | done _ => exact le_rfl
  | read key next ih =>
    have hf := hask key memory hsound
    have hr := ih (ask key memory).value (ask key memory).memory hf.2.1
    simp only [run, cost]
    rw [hf.1] at hr
    rw [hf.1]
    exact Nat.add_le_add hf.2.2 hr

end FiniteQuery

theorem rankedMemoEvaluate_resource_bounds {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (key : κ) (memory : BinaryMemo ℚ) :
    (rankedMemoEvaluate rank program bits encode key memory).freshKeys.length ≤
        (rankedMemoEvaluate rank program bits encode key memory).requests ∧
    (rankedMemoEvaluate rank program bits encode key memory).dictionaryVisits ≤
        (rankedMemoEvaluate rank program bits encode key memory).requests * (2 * (bits + 1)) ∧
    (rankedMemoEvaluate rank program bits encode key memory).memory.nodes ≤
        memory.nodes + (rankedMemoEvaluate rank program bits encode key memory).freshKeys.length * (bits + 1) := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      (rankedMemoEvaluate rank program bits encode key memory).freshKeys.length ≤
          (rankedMemoEvaluate rank program bits encode key memory).requests ∧
      (rankedMemoEvaluate rank program bits encode key memory).dictionaryVisits ≤
          (rankedMemoEvaluate rank program bits encode key memory).requests * (2 * (bits + 1)) ∧
      (rankedMemoEvaluate rank program bits encode key memory).memory.nodes ≤
          memory.nodes + (rankedMemoEvaluate rank program bits encode key memory).freshKeys.length * (bits + 1) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec, binaryMemoKey_length]
      split
      · simp only [List.length_nil, Nat.one_mul, Nat.zero_mul, Nat.add_zero]
        exact ⟨Nat.zero_le _, by omega, le_rfl⟩
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            (rankedMemoEvaluate rank program bits encode child.val previous).freshKeys.length ≤
                (rankedMemoEvaluate rank program bits encode child.val previous).requests ∧
            (rankedMemoEvaluate rank program bits encode child.val previous).dictionaryVisits ≤
                (rankedMemoEvaluate rank program bits encode child.val previous).requests * (2 * (bits + 1)) ∧
            (rankedMemoEvaluate rank program bits encode child.val previous).memory.nodes ≤
                previous.nodes + (rankedMemoEvaluate rank program bits encode child.val previous).freshKeys.length * (bits + 1) := by
          intro child previous
          exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous
        have hr := FiniteQuery.run_resource_bounds
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          (bits + 1) (2 * (bits + 1)) hchildren (program key) memory
        simp only [BinaryMemo.insertCosted_spec, binaryMemoKey_length, List.length_cons]
        have hn := BinaryMemo.insert_nodes
          (FiniteQuery.run (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).memory (binaryMemoKey bits (encode key))
          (FiniteQuery.run (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).value
        simp only [binaryMemoKey_length] at hn
        constructor
        · omega
        constructor
        · nlinarith only [hr.2.1]
        · nlinarith only [hr.2.2, hn]
  exact hall (rank key) key rfl memory

/-- Number of requests in the same adaptive program without cache hits.
It is a dominating execution tree, not the size of the full table. -/
def rankedUncachedCalls {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key}) (key : κ) : ℕ :=
  (program key).cost (fun child => rankedProgramValue rank program child.val)
    (fun child => rankedUncachedCalls rank program child.val) + 1
termination_by rank key
decreasing_by exact child.property

theorem rankedUncachedCalls_pos {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key}) (key : κ) :
    1 ≤ rankedUncachedCalls rank program key := by
  rw [rankedUncachedCalls]
  omega

theorem rankedMemoEvaluate_requests_le {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode (rankedProgramValue rank program) memory) :
    (rankedMemoEvaluate rank program bits encode key memory).requests ≤
      rankedUncachedCalls rank program key := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      memoSound bits encode (rankedProgramValue rank program) memory →
      (rankedMemoEvaluate rank program bits encode key memory).requests ≤
        rankedUncachedCalls rank program key := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmemory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · exact rankedUncachedCalls_pos rank program key
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            memoSound bits encode (rankedProgramValue rank program) previous →
            (rankedMemoEvaluate rank program bits encode child.val previous).value =
                rankedProgramValue rank program child.val ∧
            memoSound bits encode (rankedProgramValue rank program)
                (rankedMemoEvaluate rank program bits encode child.val previous).memory ∧
            (rankedMemoEvaluate rank program bits encode child.val previous).requests ≤
                rankedUncachedCalls rank program child.val := by
          intro child previous hprevious
          have hs := rankedMemoEvaluate_sound rank program bits encode hinjective hbounded
            child.val previous hprevious
          exact ⟨hs.1, hs.2, ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hprevious⟩
        have hr := FiniteQuery.run_requests_le bits encode (rankedProgramValue rank program)
          (fun child : {child : κ // rank child < rank key} => rankedProgramValue rank program child.val)
          (fun child => rankedUncachedCalls rank program child.val)
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory hmemory
        rw [rankedUncachedCalls]
        exact Nat.add_le_add_right hr 1
  exact hall (rank key) key rfl memory hsound

end EditApproximation

end OAI
