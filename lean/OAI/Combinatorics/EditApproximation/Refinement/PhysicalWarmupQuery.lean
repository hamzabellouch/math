import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoProgram
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalDependencyRank
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalWarmup
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Adaptive finite queries for the literal local initial cones and
warmup. Candidate lists are bounded local grid lists; no full target
domain is tabulated. -/

namespace EditApproximation

namespace FiniteQuery



theorem bind_value {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (next : ℚ → FiniteQuery ι) :
    (bind program next).value oracle = (next (program.value oracle)).value oracle := by
  induction program with
  | done result => rfl
  | read key continuation ih => exact ih (oracle key)



theorem collect_value {ι κ : Type*} (oracle : ι → ℚ) (reader : κ → FiniteQuery ι)
    (keys : List κ) (next : List ℚ → FiniteQuery ι) :
    (collect reader keys next).value oracle =
      (next (keys.map fun key => (reader key).value oracle)).value oracle := by
  induction keys generalizing next with
  | nil => rfl
  | cons key keys ih =>
    rw [collect, bind_value, ih]
    rfl

end FiniteQuery



theorem finiteAnswerTable_map {κ : Type*} [DecidableEq κ] (keys : List κ) (value : κ → ℚ)
    (query : κ) (hquery : query ∈ keys) :
    finiteAnswerTable keys (keys.map value) query = value query := by
  induction keys with
  | nil => simp only [List.not_mem_nil] at hquery
  | cons key keys ih =>
    simp only [List.map_cons, finiteAnswerTable]
    by_cases heq : query = key
    · subst query
      rw [ite_eq_left rfl]
    · rw [ite_eq_right heq]
      exact ih (List.mem_of_ne_of_mem heq hquery)



theorem localInitialConeCenters_raw {n : ℕ} (N P : ℕ) (A : ℚ)
    (U : TargetInterval n → ℕ) (q r : TargetInterval n)
    (hr : r ∈ localInitialConeCenters N P A U q) :
    r ∈ rawInitialConeCenters N P A (U q) q := by
  obtain ⟨b, hb, hr⟩ := List.mem_flatMap.mp hr
  exact List.mem_flatMap.mpr ⟨b, hb, (List.mem_filter.mp hr).1⟩

theorem localInitialConeCenters_congr_raw {n : ℕ} (N P : ℕ) (A : ℚ)
    (U V : TargetInterval n → ℕ) (q : TargetInterval n) (hq : U q = V q)
    (heq : ∀ r ∈ rawInitialConeCenters N P A (U q) q, U r = V r) :
    localInitialConeCenters N P A U q = localInitialConeCenters N P A V q := by
  unfold localInitialConeCenters
  rw [← hq]
  apply List.flatMap_congr
  intro b hb
  apply List.filter_congr
  intro r hr
  rw [heq r (List.mem_flatMap.mpr ⟨b, hb, hr⟩)]

theorem localInitialConeTable_congr_raw {α : Type*} (source target : List α)
    (N P F : ℕ) (A a : ℚ) (U V : TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (hq : U q = V q)
    (heq : ∀ r ∈ rawInitialConeCenters N P A (U q) q, U r = V r) :
    localInitialConeTable source target U N P F A a q =
      localInitialConeTable source target V N P F A a q := by
  have hcenters := localInitialConeCenters_congr_raw N P A U V q hq heq
  unfold localInitialConeTable
  rw [← hq, ← hcenters]
  split_ifs
  · rfl
  · congr 1
    apply List.map_congr_left
    intro r hr
    unfold initialConeValue
    rw [heq r (localInitialConeCenters_raw N P A U q r hr)]



theorem physicalInitialQuery_value {ι α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (seedRead : PhysicalEntry M J target.length → FiniteQuery ι)
    (oracle : ι → ℚ) (U : PhysicalEntry M J target.length → ℕ)
    (hseed : ∀ state, (seedRead state).value oracle = (U state : ℚ))
    (state : PhysicalEntry M J target.length) :
    (physicalInitialQuery source target N P F A seedRead state).value oracle =
      stageInitial source target U N P F A state := by
  unfold physicalInitialQuery stageInitial physicalInitialTable
  dsimp only
  split_ifs with hleaf
  · rfl
  · rw [FiniteQuery.bind_value, hseed state]
    simp only [Nat.ceil_natCast]
    rw [FiniteQuery.collect_value]
    simp only [hseed, FiniteQuery.value]
    symm
    apply localInitialConeTable_congr_raw
    · simp only [ite_true]
    · intro r hr
      by_cases heq : r = state.2
      · subst r
        simp only [ite_true]
      · rw [ite_eq_right heq, finiteAnswerTable_map _ _ r hr, Nat.ceil_natCast]

namespace PhysicalTableRequest

variable {M J ny : ℕ}



theorem combinedRank_lt_of_progress (T S : ℕ)
    (first second : PhysicalTableRequest M J ny)
    (hprogress : second.remainingDepth < first.remainingDepth ∧ second.rank T S ≤ first.rank T S ∨
      second.remainingDepth ≤ first.remainingDepth ∧ second.rank T S < first.rank T S) :
    combinedRank T S second < combinedRank T S first := by
  unfold combinedRank
  rcases hprogress with h | h
  · exact Nat.add_lt_add_of_lt_of_le h.1 h.2
  · exact Nat.add_lt_add_of_le_of_lt h.1 h.2

theorem combinedRank_sameIndexChild (T S : ℕ) (request : PhysicalTableRequest M J ny)
    (hbelow : request.node.1.val < J) (i : Fin M) (state : TargetInterval ny) :
    combinedRank T S (sameIndexChild request hbelow i state) < combinedRank T S request :=
  combinedRank_lt_of_progress T S request _ (Or.inl (sameIndexChild_progress T S request hbelow i state))

theorem combinedRank_previous_pass (T S : ℕ) (first second : PhysicalTableRequest M J ny)
    (hpass : second.pass < first.pass) (hindex : second.index ≤ T + S)
    (hnode : first.node.1.val ≤ second.node.1.val) :
    combinedRank T S second < combinedRank T S first :=
  combinedRank_lt_of_progress T S first second
    (Or.inr (previous_pass_progress T S first second hpass hindex hnode))

theorem combinedRank_warmup_child (pass copy T S j : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (i : Fin M)
    (state previousState : TargetInterval ny) (hj : 0 < j) :
    combinedRank T S (warmup pass copy (physicalChild node hbelow i) (j - 1) previousState) <
      combinedRank T S (warmup pass copy node j state) :=
  combinedRank_lt_of_progress T S _ _ (Or.inr
    ⟨(warmup_previous_child_progress pass copy T S j node hbelow i state previousState hj).1.le,
      (warmup_previous_child_progress pass copy T S j node hbelow i state previousState hj).2⟩)

end PhysicalTableRequest

end EditApproximation

end OAI
