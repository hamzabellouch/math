import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmupStepQuery
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryWork

namespace OAI

/-! Initial and warmup queries preserve reader predicates. In particular,
only same-node seed reads are needed to prove boundedness of every emitted
request; unrelated seed-table entries play no role. -/

namespace EditApproximation

theorem physicalInitialQuery_keys_all {ι α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (seedRead : PhysicalEntry M J target.length → FiniteQuery ι)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (oracle : ι → ℚ) (predicate : ι → Prop)
    (hseed : ∀ r key, key ∈ (seedRead (node, r)).keys oracle → predicate key) :
    ∀ key ∈ (physicalInitialQuery source target N P F A seedRead (node, q)).keys oracle, predicate key := by
  unfold physicalInitialQuery
  dsimp only
  split_ifs with hleaf
  · intro key hk
    exact False.elim (List.not_mem_nil hk)
  · rw [FiniteQuery.keys_bind]
    intro key hk
    rcases List.mem_append.mp hk with hfirst | hrest
    · exact hseed q key hfirst
    · apply FiniteQuery.keys_all_collect oracle predicate _ _ _ ?_ ?_ key hrest
      · intro r _ other ho
        exact hseed r other ho
      · intro answers other ho
        exact False.elim (List.not_mem_nil ho)

theorem localWarmupStepQuery_keys_all {ι : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : ℚ) (initialRead : TargetInterval ny → FiniteQuery ι)
    (childRead : Fin M × TargetInterval ny → FiniteQuery ι) (q : TargetInterval ny)
    (oracle : ι → ℚ) (predicate : ι → Prop)
    (hinitial : ∀ r key, key ∈ (initialRead r).keys oracle → predicate key)
    (hchild : ∀ input key, key ∈ (childRead input).keys oracle → predicate key) :
    ∀ key ∈ (localWarmupStepQuery parent N P F a initialRead childRead q).keys oracle, predicate key := by
  unfold localWarmupStepQuery
  rw [FiniteQuery.keys_bind]
  intro key hk
  rcases List.mem_append.mp hk with hfirst | hrest
  · exact hinitial q key hfirst
  · apply FiniteQuery.keys_all_collect oracle predicate _ _ _ ?_ ?_ key hrest
    · intro r _ other ho
      exact hinitial r other ho
    · intro initialValues
      apply FiniteQuery.keys_all_collect
      · intro input _ other ho
        exact hchild input other ho
      · intro childValues other ho
        exact False.elim (List.not_mem_nil ho)

theorem physicalWarmupRequestQuery_keys_all {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (pass copy T S j : ℕ) (node : PhysicalNode M J) (q : TargetInterval target.length)
    (seedRead : PhysicalEntry M J target.length →
      FiniteQuery {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < (PhysicalTableRequest.warmup pass copy node j q).combinedRank T S})
    (oracle) (predicate : PhysicalTableRequest M J target.length → Prop)
    (hseed : ∀ r key, key ∈ (seedRead (node, r)).keys oracle → predicate key.val)
    (hchild : ∀ (hbelow : node.1.val < J) (input : Fin M × TargetInterval target.length),
      predicate (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow input.1) (j - 1) input.2)) :
    ∀ key ∈ (physicalWarmupRequestQuery source target N P F A pass copy T S j node q seedRead).keys oracle,
      predicate key.val := by
  cases j with
  | zero => exact physicalInitialQuery_keys_all source target N P F A seedRead node q oracle _ hseed
  | succ j =>
    dsimp only [physicalWarmupRequestQuery]
    split_ifs with hbelow hleaf
    · exact physicalInitialQuery_keys_all source target N P F A seedRead node q oracle _ hseed
    · unfold physicalWarmupStepQuery
      apply localWarmupStepQuery_keys_all
      · intro r
        exact physicalInitialQuery_keys_all source target N P F A seedRead node r oracle _ hseed
      · intro input key hk
        simp only [physicalWarmupChildQuery, FiniteQuery.keys, List.mem_singleton] at hk
        subst key
        exact hchild hbelow input
    · exact physicalInitialQuery_keys_all source target N P F A seedRead node q oracle _ hseed

theorem physicalWarmupRequestQuery_keys_bounded {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (passes copies pass copy T S j : ℕ) (hpass : pass < passes) (hcopy : copy < copies) (hj : j ≤ T)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (seedRead : PhysicalEntry M J target.length →
      FiniteQuery {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < (PhysicalTableRequest.warmup pass copy node j q).combinedRank T S})
    (oracle)
    (hseed : ∀ r key, key ∈ (seedRead (node, r)).keys oracle → key.val.Bounded passes copies T S) :
    ∀ key ∈ (physicalWarmupRequestQuery source target N P F A pass copy T S j node q seedRead).keys oracle,
      key.val.Bounded passes copies T S := by
  apply physicalWarmupRequestQuery_keys_all source target N P F A pass copy T S j node q seedRead oracle _ hseed
  intro hbelow input
  exact PhysicalTableRequest.warmup_bounded passes copies pass copy (physicalChild node hbelow input.1)
    T S (j - 1) input.2 hpass hcopy (by omega)

end EditApproximation

end OAI
