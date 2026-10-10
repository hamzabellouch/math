import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPreparedCompletion
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedParentSpent

namespace OAI

namespace LowSpaceSubsetSum.BudgetedPreparedParent

variable {n : ℕ}

theorem runContexts_spent (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (fuel₀ fuel₁ control : ℕ)
    (left : PreparedReaderContext.Context I F P .direct)
    (right : PreparedReaderContext.Context I F P (.complementary t)) (budget : ℕ)
    (hn : 10000 ≤ n) (hd₀ : left.depth ≤ n) (hd₁ : right.depth ≤ n)
    (hcopy : (12 * n + 32) * 2 ^ (right.depth + 1) ≤ B)
    (out : PreparedParentExecution.Result I C) (remaining : ℕ)
    (h : (runContexts I F P t C B fuel₀ fuel₁ control left right budget).1 = some (out, remaining)) :
    (runContexts I F P t C B fuel₀ fuel₁ control left right budget).2 ≤ budget - remaining := by
  obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
  rcases p with ⟨value, rest⟩
  have hs := BudgetedParentJoin.run_spent I F P t C B left.right right.right
    fuel₀ fuel₁ control left.state right.state budget hn hd₀ hd₁ hcopy value rest hp
  cases he
  exact hs

theorem run_spent (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B C budget : ℕ) (hn : 10000 ≤ n)
    (hl : ∀ j, (D.pair j).left.occurrences.card ≤ C)
    (hr : ∀ j, (D.pair j).right.occurrences.card ≤ C) (hC : C ≤ 2 ^ n)
    (hcopy : (12 * n + 32) *
      2 ^ (Nat.clog 2 ({D with maskRestriction := P.semantic}.pair 1).leftArray.size + 1) ≤ B)
    (out : PreparedParentExecution.Result D.input D.capacity) (remaining : ℕ)
    (h : (run D F P hF B C budget).1 = some (out, remaining)) :
    (run D F P hF B C budget).2 ≤ budget - remaining := by
  have h₀ := PreparedReaderContext.build_work D F P hF 0 C hn (hl 0) (hr 0) hC
  have h₁ := PreparedReaderContext.build_work D F P hF 1 C hn (hl 1) (hr 1) hC
  have hf := ComputedParentFuels.run_scale D hn
  have hd₀ := PreparedReaderContext.build_depth D F P hF 0 ((hl 0).trans hC)
  have hd₁ := PreparedReaderContext.build_depth D F P hF 1 ((hl 1).trans hC)
  have hc : (12 * n + 32) * 2 ^ ((PreparedReaderContext.build D F P hF 1).1.depth + 1) ≤ B := by
    rw [PreparedReaderContext.build_value]
    exact hcopy
  rw [run] at h ⊢
  split at h
  next hb =>
    simp only [hb, ↓reduceIte] at h ⊢
    have hv := (runContexts_value D.input F D.modulus D.parentResidue D.capacity B
      (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second (ComputedParentFuels.run D).1.control
      (PreparedReaderContext.build D F P hF 0).1 (PreparedReaderContext.build D F P hF 1).1
      (budget - setupCharge D.input C) out remaining h).2
    have hs := runContexts_spent D.input F D.modulus D.parentResidue D.capacity B
      (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second (ComputedParentFuels.run D).1.control
      (PreparedReaderContext.build D F P hF 0).1 (PreparedReaderContext.build D F P hF 1).1
      (budget - setupCharge D.input C) hn hd₀ hd₁ hc out remaining h
    change (ComputedParentFuels.run D).2 + (PreparedReaderContext.build D F P hF 0).2 +
      (PreparedReaderContext.build D F P hF 1).2 +
      (runContexts D.input F D.modulus D.parentResidue D.capacity B
        (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second (ComputedParentFuels.run D).1.control
        (PreparedReaderContext.build D F P hF 0).1 (PreparedReaderContext.build D F P hF 1).1
        (budget - setupCharge D.input C)).2 + 7 ≤ budget - remaining
    unfold setupCharge at hb hv hs ⊢
    simp only [Nat.mul_assoc] at hb hv hs ⊢
    omega
  next _ => simp only [reduceCtorEq] at h

end LowSpaceSubsetSum.BudgetedPreparedParent

end OAI
