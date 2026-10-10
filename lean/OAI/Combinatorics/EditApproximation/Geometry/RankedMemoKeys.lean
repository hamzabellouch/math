import OAI.Combinatorics.EditApproximation.Geometry.ChargedCoarseOracle
import OAI.Combinatorics.EditApproximation.Geometry.SourceErasure

namespace OAI

/-! A cache miss is among the requests of the uncached execution with
identical answers. This includes adaptive continuations and cache hits. -/

namespace EditApproximation

namespace FiniteQuery

theorem substitute_keys {ι κ : Type*} (ask : ι → FiniteQuery κ) (oracle : κ → ℚ)
    (query : FiniteQuery ι) :
    (query.substitute ask).keys oracle =
      (query.keys (fun key => (ask key).value oracle)).flatMap (fun key => (ask key).keys oracle) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    simp only [substitute, keys_bind, keys, List.flatMap_cons]
    rw [ih]

theorem run_freshKeys_mem {ι κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → ℚ) (answer : ι → ℚ) (allowed : ι → List κ)
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, memoSound bits encode expected memory →
      (ask key memory).value = answer key ∧
      memoSound bits encode expected (ask key memory).memory ∧
      ∀ item ∈ (ask key memory).freshKeys, item ∈ allowed key)
    (query : FiniteQuery ι) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode expected memory) :
    ∀ item ∈ (run ask query memory).freshKeys, item ∈ (query.keys answer).flatMap allowed := by
  induction query generalizing memory with
  | done value => simp only [run, List.not_mem_nil, false_implies, implies_true]
  | read key next ih =>
    have hf := hask key memory hsound
    intro item hitem
    simp only [run, List.mem_append] at hitem
    rcases hitem with hfirst | hrest
    · exact List.mem_flatMap.mpr ⟨key, List.mem_cons_self, hf.2.2 item hfirst⟩
    · have hr := ih (ask key memory).value (ask key memory).memory hf.2.1 item hrest
      rw [hf.1] at hr
      obtain ⟨child, hc, hi⟩ := List.mem_flatMap.mp hr
      exact List.mem_flatMap.mpr ⟨child, List.mem_cons_of_mem key hc, hi⟩

theorem eraseSources_inr_mem_iff {σ κ : Type*} (source : σ → ℚ) (table : κ → ℚ)
    (query : FiniteQuery (Sum σ κ)) (key : κ) :
    Sum.inr key ∈ query.keys (Sum.elim source table) ↔
      key ∈ (eraseSources source query).keys table := by
  induction query with
  | done value => simp only [keys, eraseSources, List.not_mem_nil]
  | read next continuation ih =>
    cases next with
    | inl scalar => simpa only [keys, eraseSources, Sum.elim_inl, List.mem_cons,
        Sum.inr_ne_inl, false_or] using ih (source scalar)
    | inr child => simpa only [keys, eraseSources, Sum.elim_inr, List.mem_cons,
        Sum.inr.injEq] using or_congr Iff.rfl (ih (table child))

end FiniteQuery

def rankedUncachedKeys {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key}) (key : κ) : List κ :=
  key :: ((program key).keys (fun child => rankedProgramValue rank program child.val)).flatMap
    (fun child => rankedUncachedKeys rank program child.val)
termination_by rank key
decreasing_by exact child.property

theorem rankedMemoEvaluate_freshKeys_mem {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode (rankedProgramValue rank program) memory) :
    ∀ item ∈ (rankedMemoEvaluate rank program bits encode key memory).freshKeys,
      item ∈ rankedUncachedKeys rank program key := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      memoSound bits encode (rankedProgramValue rank program) memory →
      ∀ item ∈ (rankedMemoEvaluate rank program bits encode key memory).freshKeys,
        item ∈ rankedUncachedKeys rank program key := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmemory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · simp
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            memoSound bits encode (rankedProgramValue rank program) previous →
            (rankedMemoEvaluate rank program bits encode child.val previous).value =
                rankedProgramValue rank program child.val ∧
            memoSound bits encode (rankedProgramValue rank program)
                (rankedMemoEvaluate rank program bits encode child.val previous).memory ∧
            ∀ item ∈ (rankedMemoEvaluate rank program bits encode child.val previous).freshKeys,
              item ∈ rankedUncachedKeys rank program child.val := by
          intro child previous hp
          have hs := rankedMemoEvaluate_sound rank program bits encode hinjective hbounded child.val previous hp
          exact ⟨hs.1, hs.2, ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp⟩
        have hr := FiniteQuery.run_freshKeys_mem bits encode (rankedProgramValue rank program)
          (fun child : {child : κ // rank child < rank key} => rankedProgramValue rank program child.val)
          (fun child => rankedUncachedKeys rank program child.val)
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory hmemory
        intro item hi
        simp only [List.mem_cons] at hi
        rw [rankedUncachedKeys]
        rcases hi with rfl | hi
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem key (hr item hi)
  exact hall (rank key) key rfl memory hsound

end EditApproximation

end OAI
