import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPreparedParent
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedParentRemaining

namespace OAI

namespace LowSpaceSubsetSum.BudgetedPreparedParent

variable {n : ℕ}

theorem runContexts_complete (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (fuel₀ fuel₁ control : ℕ)
    (left : PreparedReaderContext.Context I F P .direct)
    (right : PreparedReaderContext.Context I F P (.complementary t)) (budget : ℕ) (hn : 10000 ≤ n)
    (hb : let out := (PreparedParentExecution.runContexts I F P t C B fuel₀ fuel₁ control left right).1
      inputScale I ^ 7 * out.queries + B * out.copies + 4 ≤ budget) :
    ∃ remaining, (runContexts I F P t C B fuel₀ fuel₁ control left right budget).1 =
      some ((PreparedParentExecution.runContexts I F P t C B fuel₀ fuel₁ control left right).1, remaining) := by
  obtain ⟨remaining, h⟩ := BudgetedParentJoin.run_complete I F P t C B left.right right.right
    fuel₀ fuel₁ control left.state right.state budget hn hb
  refine ⟨remaining, ?_⟩
  simp only [runContexts, h, Option.map_some]
  rfl

theorem runContexts_remaining (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (fuel₀ fuel₁ control : ℕ)
    (left : PreparedReaderContext.Context I F P .direct)
    (right : PreparedReaderContext.Context I F P (.complementary t)) (budget : ℕ) (hn : 10000 ≤ n)
    (out : PreparedParentExecution.Result I C) (remaining : ℕ)
    (h : (runContexts I F P t C B fuel₀ fuel₁ control left right budget).1 = some (out, remaining)) :
    budget ≤ remaining + inputScale I ^ 7 * out.queries + B * out.copies + 4 := by
  obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
  rcases p with ⟨value, rest⟩
  have hr := BudgetedParentJoin.run_remaining I F P t C B left.right right.right
    fuel₀ fuel₁ control left.state right.state budget hn value rest hp
  cases he
  exact hr

theorem run_complete (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B C budget : ℕ) (hn : 10000 ≤ n)
    (hb : setupCharge D.input C +
      inputScale D.input ^ 7 * ({D with maskRestriction := P.semantic}.collect B).state.queries +
      B * ({D with maskRestriction := P.semantic}.collect B).state.copies + 4 ≤ budget) :
    ∃ remaining, (run D F P hF B C budget).1 =
      some ((ComputedParentExecution.run D F P hF B).1, remaining) := by
  have hs : setupCharge D.input C ≤ budget := by omega
  have hc := ComputedParentExecution.run_value D F P hF B
  change (PreparedParentExecution.runContexts D.input F D.modulus D.parentResidue D.capacity B
      (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second (ComputedParentFuels.run D).1.control
      (PreparedReaderContext.build D F P hF 0).1 (PreparedReaderContext.build D F P hF 1).1).1 = _ at hc
  have hcount := StoredParentExecution.collect_value {D with maskRestriction := P.semantic} F hF B
  have hq := congrArg (fun o => o.state.queries) hcount
  have hcp := congrArg (fun o => o.state.copies) hcount
  change (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).1.state.queries = _ at hq
  change (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).1.state.copies = _ at hcp
  obtain ⟨remaining, hr⟩ := runContexts_complete D.input F D.modulus D.parentResidue D.capacity B
    (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second (ComputedParentFuels.run D).1.control
    (PreparedReaderContext.build D F P hF 0).1 (PreparedReaderContext.build D F P hF 1).1
    (budget - setupCharge D.input C) hn (by
      rw [hc]
      change inputScale D.input ^ 7 *
        (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).1.state.queries +
        B * (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).1.state.copies + 4 ≤ _
      rw [hq, hcp]
      omega)
  exact ⟨remaining, by simpa only [run, hs, ↓reduceIte, ComputedParentExecution.run, PreparedParentExecution.collect] using hr⟩

theorem run_remaining (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B C budget : ℕ) (hn : 10000 ≤ n)
    (out : PreparedParentExecution.Result D.input D.capacity) (remaining : ℕ)
    (h : (run D F P hF B C budget).1 = some (out, remaining)) :
    budget ≤ remaining + setupCharge D.input C + inputScale D.input ^ 7 * out.queries + B * out.copies + 4 := by
  rw [run] at h
  split at h
  next hb =>
    have hr := runContexts_remaining D.input F D.modulus D.parentResidue D.capacity B
      (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second (ComputedParentFuels.run D).1.control
      (PreparedReaderContext.build D F P hF 0).1 (PreparedReaderContext.build D F P hF 1).1
      (budget - setupCharge D.input C) hn out remaining h
    omega
  next _ => contradiction

end LowSpaceSubsetSum.BudgetedPreparedParent

end OAI
