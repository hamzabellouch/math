import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoWork
import OAI.Combinatorics.EditApproximation.Numerics.NumericalWork
import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedProgram

namespace OAI

/-! Every value retained by the actual binary dictionary obeys the
semantic value bound. This includes every allocated path, not only keys
queried after the computation. -/

namespace EditApproximation
namespace BinaryMemo

def AllValues {α : Type*} (P : α → Prop) (memory : BinaryMemo α) : Prop :=
  ∀ key value, memory.lookup key = some value → P value

theorem allValues_empty {α : Type*} (P : α → Prop) : AllValues P (.empty : BinaryMemo α) := by
  intro key value h
  rw [lookup_empty] at h
  cases h

theorem AllValues.insert {α : Type*} {P : α → Prop} {memory : BinaryMemo α}
    (hmem : AllValues P memory) (key : List Bool) (a : α) (ha : P a) :
    AllValues P (memory.insert key a) := by
  intro query value hvalue
  by_cases heq : query = key
  · subst query
    rw [lookup_insert_same] at hvalue
    cases hvalue
    exact ha
  · rw [lookup_insert_other memory key query a heq] at hvalue
    exact hmem query value hvalue

/-- One word each for the tag and two child pointers, plus the value bits.
Counting bits individually is an upper bound on logarithmic-word storage. -/
def rationalStorage : BinaryMemo ℚ → ℕ
  | .empty => 0
  | .node value left right =>
    3 + (value.map rationalEncodingBits).getD 0 + left.rationalStorage + right.rationalStorage

theorem rationalStorage_le (memory : BinaryMemo ℚ) (W : ℕ)
    (hmem : AllValues (fun value => rationalEncodingBits value ≤ W) memory) :
    memory.rationalStorage ≤ (W + 3) * memory.nodes := by
  induction memory with
  | empty => simp only [rationalStorage, nodes, Nat.mul_zero, le_refl]
  | node value left right ihl ihr =>
    have hl : AllValues (fun value => rationalEncodingBits value ≤ W) left := by
      intro key value h
      exact hmem (false :: key) value h
    have hr : AllValues (fun value => rationalEncodingBits value ≤ W) right := by
      intro key value h
      exact hmem (true :: key) value h
    have hv : (value.map rationalEncodingBits).getD 0 ≤ W := by
      cases value with
      | none => exact Nat.zero_le _
      | some value => exact hmem [] value rfl
    have hl' := ihl hl
    have hr' := ihr hr
    simp only [rationalStorage, nodes]
    nlinarith only [hv, hl', hr']

end BinaryMemo

namespace FiniteQuery

theorem run_invariant {ι κ : Type*} (invariant : BinaryMemo ℚ → Prop)
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, invariant memory → invariant (ask key memory).memory)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ) (hmem : invariant memory) :
    invariant (run ask program memory).memory := by
  induction program generalizing memory with
  | done value => exact hmem
  | read key next ih => exact ih (ask key memory).value _ (hask key memory hmem)

end FiniteQuery

 theorem rankedMemoEvaluate_allValues {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (P : ℚ → Prop)
    (hvalue : ∀ key, P (rankedProgramValue rank program key))
    (key : κ) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode (rankedProgramValue rank program) memory)
    (hmem : BinaryMemo.AllValues P memory) :
    BinaryMemo.AllValues P (rankedMemoEvaluate rank program bits encode key memory).memory := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      memoSound bits encode (rankedProgramValue rank program) memory →
      BinaryMemo.AllValues P memory →
      BinaryMemo.AllValues P (rankedMemoEvaluate rank program bits encode key memory).memory := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hsound hmem
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · exact hmem
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            memoSound bits encode (rankedProgramValue rank program) previous →
            BinaryMemo.AllValues P previous →
            memoSound bits encode (rankedProgramValue rank program)
                (rankedMemoEvaluate rank program bits encode child.val previous).memory ∧
              BinaryMemo.AllValues P
                (rankedMemoEvaluate rank program bits encode child.val previous).memory := by
          intro child previous hs hm
          exact ⟨(rankedMemoEvaluate_sound rank program bits encode hinjective hbounded _ _ hs).2,
            ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hs hm⟩
        have hrun := FiniteQuery.run_invariant
          (fun previous => memoSound bits encode (rankedProgramValue rank program) previous ∧
            BinaryMemo.AllValues P previous)
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          (fun child previous h => hchildren child previous h.1 h.2) (program key) memory ⟨hsound, hmem⟩
        have hresult := (FiniteQuery.run_sound bits encode (rankedProgramValue rank program)
          (fun child : {child : κ // rank child < rank key} => rankedProgramValue rank program child.val)
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          (fun child previous hs => rankedMemoEvaluate_sound rank program bits encode hinjective hbounded
            child.val previous hs) (program key) memory hsound).1
        have hv : (FiniteQuery.run
            (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).value = rankedProgramValue rank program key := by
          rw [rankedProgramValue]
          exact hresult
        simp only [BinaryMemo.insertCosted_spec]
        exact hrun.2.insert _ _ (hv.symm ▸ hvalue key)
  exact hall (rank key) key rfl memory hsound hmem

namespace SourceRanked

theorem memo_allValues {σ κ : Type*} (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
      tableValue key) (bits : ℕ) (encode : Sum σ κ → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (P : ℚ → Prop) (hvalue : ∀ key, P (value sourceValue tableValue key)) (key : Sum σ κ) :
    BinaryMemo.AllValues P (rankedMemoEvaluate (rank tableRank) (body tableRank tableBody sourceValue)
      bits encode key .empty).memory := by
  apply rankedMemoEvaluate_allValues _ _ bits encode hinjective hbounded P
    (fun key => ?_) key .empty (memoSound_empty _ _ _) (BinaryMemo.allValues_empty P)
  rw [program_value tableRank tableBody sourceValue tableValue hbody]
  exact hvalue key

end SourceRanked
end EditApproximation

end OAI
