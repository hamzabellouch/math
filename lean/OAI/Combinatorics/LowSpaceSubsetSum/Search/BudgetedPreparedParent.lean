import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedParentJoin
import OAI.Combinatorics.LowSpaceSubsetSum.Search.ComputedParentExecution

namespace OAI

/-! # Prepaid shared-array setup and parent collection -/

namespace LowSpaceSubsetSum.BudgetedPreparedParent

variable {n : ℕ}

/-- This reserve covers the two initializations, the scalar loop limits,
and the fixed wrapper bookkeeping. -/
def setupCharge (I : Instance n) (C : ℕ) : ℕ :=
  2 * inputScale I ^ 9 * (C + 1) + inputScale I ^ 3 + 12

def runContexts (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (fuel₀ fuel₁ control : ℕ)
    (left : PreparedReaderContext.Context I F P .direct)
    (right : PreparedReaderContext.Context I F P (.complementary t)) (budget : ℕ) :=
  let out := BudgetedParentJoin.run I F P t C B left.right right.right
    fuel₀ fuel₁ control left.state right.state budget
  (out.1.map (fun (value, remaining) => (PreparedParentExecution.project value, remaining)), out.2)

def run (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B C budget : ℕ) :
    Option (PreparedParentExecution.Result D.input D.capacity × ℕ) × ℕ :=
  if setupCharge D.input C ≤ budget then
    let limits := ComputedParentFuels.run D
    let left := PreparedReaderContext.build D F P hF 0
    let right := PreparedReaderContext.build D F P hF 1
    let out := runContexts D.input F D.modulus D.parentResidue D.capacity B
      limits.1.first limits.1.second limits.1.control left.1 right.1 (budget - setupCharge D.input C)
    (out.1, limits.2 + left.2 + right.2 + out.2 + 7)
  else (none, 1)

theorem runContexts_value (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (fuel₀ fuel₁ control : ℕ)
    (left : PreparedReaderContext.Context I F P .direct)
    (right : PreparedReaderContext.Context I F P (.complementary t)) (budget : ℕ)
    (out : PreparedParentExecution.Result I C) (remaining : ℕ)
    (h : (runContexts I F P t C B fuel₀ fuel₁ control left right budget).1 = some (out, remaining)) :
    out = (PreparedParentExecution.runContexts I F P t C B fuel₀ fuel₁ control left right).1 ∧
      remaining ≤ budget := by
  obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
  rcases p with ⟨value, rest⟩
  have hv := BudgetedParentJoin.run_value I F P t C B left.right right.right
    fuel₀ fuel₁ control left.state right.state budget value rest hp
  cases he
  exact ⟨congrArg PreparedParentExecution.project hv.1, hv.2⟩

theorem run_value (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B C budget : ℕ)
    (out : PreparedParentExecution.Result D.input D.capacity) (remaining : ℕ)
    (h : (run D F P hF B C budget).1 = some (out, remaining)) :
    out = (ComputedParentExecution.run D F P hF B).1 ∧ remaining ≤ budget := by
  rw [run] at h
  split at h
  next hb =>
    have hv := runContexts_value D.input F D.modulus D.parentResidue D.capacity B
      (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second
      (ComputedParentFuels.run D).1.control
      (PreparedReaderContext.build D F P hF 0).1 (PreparedReaderContext.build D F P hF 1).1
      (budget - setupCharge D.input C) out remaining h
    exact ⟨hv.1, hv.2.trans (Nat.sub_le _ _)⟩
  next _ => contradiction

theorem run_work (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B C budget : ℕ) (hn : 10000 ≤ n)
    (hl : ∀ j, (D.pair j).left.occurrences.card ≤ C)
    (hr : ∀ j, (D.pair j).right.occurrences.card ≤ C) (hC : C ≤ 2 ^ n)
    (hcopy : (12 * n + 32) *
      2 ^ (Nat.clog 2 ({D with maskRestriction := P.semantic}.pair 1).leftArray.size + 1) ≤ B) :
    (run D F P hF B C budget).2 ≤ budget + 1 := by
  have h₀ := PreparedReaderContext.build_work D F P hF 0 C hn (hl 0) (hr 0) hC
  have h₁ := PreparedReaderContext.build_work D F P hF 1 C hn (hl 1) (hr 1) hC
  have hf := ComputedParentFuels.run_scale D hn
  have hd₀ := PreparedReaderContext.build_depth D F P hF 0 ((hl 0).trans hC)
  have hd₁ := PreparedReaderContext.build_depth D F P hF 1 ((hl 1).trans hC)
  have hc : (12 * n + 32) * 2 ^ ((PreparedReaderContext.build D F P hF 1).1.depth + 1) ≤ B := by
    rw [PreparedReaderContext.build_value]
    exact hcopy
  rw [run]
  split
  next hb =>
    have hw := BudgetedParentJoin.run_work D.input F D.modulus D.parentResidue D.capacity B
      (PreparedReaderContext.build D F P hF 0).1.right (PreparedReaderContext.build D F P hF 1).1.right
      (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second
      (ComputedParentFuels.run D).1.control
      (PreparedReaderContext.build D F P hF 0).1.state (PreparedReaderContext.build D F P hF 1).1.state
      (budget - setupCharge D.input C) hn hd₀ hd₁ hc
    change (ComputedParentFuels.run D).2 + (PreparedReaderContext.build D F P hF 0).2 +
      (PreparedReaderContext.build D F P hF 1).2 +
      (BudgetedParentJoin.run D.input F D.modulus D.parentResidue D.capacity B
        (PreparedReaderContext.build D F P hF 0).1.right (PreparedReaderContext.build D F P hF 1).1.right
        (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second
        (ComputedParentFuels.run D).1.control
        (PreparedReaderContext.build D F P hF 0).1.state (PreparedReaderContext.build D F P hF 1).1.state
        (budget - setupCharge D.input C)).2 + 7 ≤ budget + 1
    unfold setupCharge at hb hw ⊢
    simp only [Nat.mul_assoc] at hb hw ⊢
    omega
  next _ => dsimp only; omega

end LowSpaceSubsetSum.BudgetedPreparedParent

end OAI
