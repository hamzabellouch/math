import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedParentCollector
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPrefixCompletion
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPrefixLedger

namespace OAI

namespace LowSpaceSubsetSum.BudgetedConcretePrefix

variable {n : ℕ}

def run (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (check : Array (StoredEntry n) → ℕ → Option (Bool × ℕ) × ℕ)
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ) :=
  BudgetedPrefixController.run (BudgetedParentCollector.collect D F hF B D.capacity)
    check order P budget

theorem value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (check : Array (StoredEntry n) → ℕ → Option (Bool × ℕ) × ℕ)
    (pureCheck : Array (StoredEntry n) → Bool × ℕ)
    (checkValue : Array (Entry (Fin n)) → Bool)
    (hc : ∀ a b v left, (check a b).1 = some (v, left) → v = (pureCheck a).1 ∧ left ≤ b)
    (hp : ∀ a, (pureCheck a).1 = checkValue (a.map StoredEntry.semantic))
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ) (v : Bool) (left : ℕ)
    (h : (run D F hF B check order P budget).1 = some (v, left)) :
    v = D.searchRight B checkValue order P.semantic ∧ left ≤ budget := by
  let pureCollect := fun P => ((ComputedParentExecution.run D F P hF B).1.dictionary, 0)
  have hv := BudgetedPrefixController.run_value
    (BudgetedParentCollector.collect D F hF B D.capacity) pureCollect check pureCheck
    (BudgetedParentCollector.value D F hF B D.capacity) hc order P budget v left h
  rw [StoredPrefixController.run_value D B pureCollect
    (fun P => ComputedParentExecution.dictionary_value D F P hF B) pureCheck checkValue hp] at hv
  exact hv

theorem account (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (check : Array (StoredEntry n) → ℕ → Option (Bool × ℕ) × ℕ)
    (hc : ∀ a b, BudgetedSeparatorFlow.Account b (check a b))
    (hn : 10000 ≤ n) (hl : ∀ j, (D.pair j).left.occurrences.card ≤ D.capacity)
    (hr : ∀ j, (D.pair j).right.occurrences.card ≤ D.capacity) (hC : D.capacity ≤ 2 ^ n)
    (hcopy : ∀ P : StoredRestriction n, (12 * n + 32) *
      2 ^ (Nat.clog 2 ({D with maskRestriction := P.semantic}.pair 1).leftArray.size + 1) ≤ B)
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ) :
    BudgetedSeparatorFlow.Account budget (run D F hF B check order P budget) :=
  BudgetedPrefixController.run_account _ check
    (fun P b => BudgetedParentCollector.account D F hF B D.capacity P b hn hl hr hC (hcopy P))
    hc order P budget

noncomputable def allowance (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (checkBill : Array (StoredEntry n) → ℕ)
    (order : List (Fin n)) (P : StoredRestriction n) :=
  BudgetedPrefixController.allowance
    (fun P => (ComputedParentExecution.run D F P hF B).1.dictionary)
    (BudgetedParentCollector.bill D B D.capacity) checkBill order P

theorem complete (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (check : Array (StoredEntry n) → ℕ → Option (Bool × ℕ) × ℕ)
    (checkBill : Array (StoredEntry n) → ℕ)
    (hc : ∀ a b, checkBill a ≤ b → ∃ v left, (check a b).1 = some (v, left))
    (hr : ∀ a b v left, (check a b).1 = some (v, left) → b ≤ left + checkBill a)
    (hn : 10000 ≤ n) (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ)
    (hb : allowance D F hF B checkBill order P ≤ budget) :
    ∃ v left, (run D F hF B check order P budget).1 = some (v, left) :=
  BudgetedPrefixController.run_complete _ _ check _ checkBill
    (fun P b h => BudgetedParentCollector.complete D F hF B D.capacity P b hn h)
    (fun P b d l h => ⟨(BudgetedParentCollector.value D F hF B D.capacity P b d l h).1,
      BudgetedParentCollector.remaining D F hF B D.capacity P b hn d l h⟩)
    hc hr order P budget hb

theorem remaining (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (check : Array (StoredEntry n) → ℕ → Option (Bool × ℕ) × ℕ)
    (checkBill : Array (StoredEntry n) → ℕ)
    (hr : ∀ a b v left, (check a b).1 = some (v, left) → b ≤ left + checkBill a)
    (hn : 10000 ≤ n) (order : List (Fin n)) (P : StoredRestriction n)
    (budget : ℕ) (v : Bool) (left : ℕ)
    (h : (run D F hF B check order P budget).1 = some (v, left)) :
    budget ≤ left + allowance D F hF B checkBill order P :=
  BudgetedPrefixController.run_remaining _ _ check _ checkBill
    (fun P b d l h => ⟨(BudgetedParentCollector.value D F hF B D.capacity P b d l h).1,
      BudgetedParentCollector.remaining D F hF B D.capacity P b hn d l h⟩)
    hr order P budget v left h

theorem allowance_ledger (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (checkBill : Array (StoredEntry n) → ℕ)
    (semanticCheckBill : Array (Entry (Fin n)) → ℕ)
    (hcheck : ∀ a, checkBill a = semanticCheckBill (a.map StoredEntry.semantic))
    (order : List (Fin n)) (P : StoredRestriction n) :
    allowance D F hF B checkBill order P ≤
      ((2 * inputScale D.input ^ 9 + inputScale D.input ^ 3 + 16) * (D.capacity + 1) +
        StoredPrefixController.header n) * D.taskStarts B order P.semantic +
      inputScale D.input ^ 7 * (D.prefixLedger B order P.semantic).queries +
      B * (D.prefixLedger B order P.semantic).copies +
      ((D.completedArrays B order P.semantic).map semanticCheckBill).sum := by
  have h := BudgetedPrefixController.allowance_le_ledger D B
    (fun P => (ComputedParentExecution.run D F P hF B).1.dictionary)
    (fun P => ComputedParentExecution.dictionary_value D F P hF B)
    (BudgetedParentCollector.bill D B D.capacity) checkBill semanticCheckBill hcheck
    (2 * inputScale D.input ^ 9 + inputScale D.input ^ 3 + 16) (inputScale D.input ^ 7) 0 B
    (fun P => by
      unfold BudgetedParentCollector.bill BudgetedPreparedParent.setupCharge
      simp only [RepresentationParentData.localLedger, Nat.zero_mul, Nat.add_zero]
      have hscale : inputScale D.input ^ 3 + 16 ≤
          (inputScale D.input ^ 3 + 16) * (D.capacity + 1) := Nat.le_mul_of_pos_right _ (by omega)
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at hscale ⊢
      omega) order P
  simpa only [allowance, Nat.zero_mul, Nat.add_zero] using h

end LowSpaceSubsetSum.BudgetedConcretePrefix

end OAI
