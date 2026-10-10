import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorCheckAllowance
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorRemaining

namespace OAI

/-! # Guarded array-to-list entry to the prepared checker

The dictionary arrays and prepared tables remain shared. Conversion to
temporary pointer lists is prepaid using the two constant-time array sizes.
No temporary list is created on the insufficient-budget branch.
-/

namespace LowSpaceSubsetSum.BudgetedSeparatorArrays

open BudgetedSeparatorCall BudgetedSeparatorFlow StoredSeparatorCheck

variable {n g : ℕ}

def conversionCharge (left right : Array (StoredEntry n)) : ℕ :=
  2 * (left.size + right.size) + 5

def convert (left right : Array (StoredEntry n)) (budget : ℕ) :
    Outcome (List (StoredEntry n) × List (StoredEntry n)) :=
  BudgetedSeparatorCall.run (conversionCharge left right)
    (fun _ => ((left.toList, right.toList), 2 * (left.size + right.size) + 4)) budget

def execute (capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (left right : Array (StoredEntry n)) (budget : ℕ) : Outcome Bool :=
  bind (convert left right budget) fun lists remaining =>
    BudgetedSeparatorCheck.execute capacity target blocks lists.1 lists.2
      left.size right.size remaining

theorem account (capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (left right : Array (StoredEntry n)) (budget : ℕ) :
    Account budget (execute capacity target blocks left right budget) := by
  apply bind_account
  · exact ⟨BudgetedSeparatorCall.work _ _ _ (by rfl),
      fun p rem hp => BudgetedSeparatorCall.spent _ _ _ (by rfl) p rem hp⟩
  · intro lists remaining h
    obtain ⟨rfl, _, _⟩ := BudgetedSeparatorCall.value _ _ _ _ _ h
    exact BudgetedSeparatorCheck.account capacity target blocks left.toList right.toList
      left.size right.size remaining (by simp) (by simp)

def allowance (capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (left right : Array (StoredEntry n)) : ℕ :=
  conversionCharge left right +
    (BudgetedSeparatorCheck.reference capacity target blocks left.toList right.toList).2

theorem complete (capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (left right : Array (StoredEntry n)) (budget : ℕ)
    (hb : allowance capacity target blocks left right ≤ budget) :
    (execute capacity target blocks left right budget).1 =
      some ((BudgetedSeparatorCheck.reference capacity target blocks left.toList right.toList).1,
        budget - allowance capacity target blocks left right) := by
  have hc : conversionCharge left right ≤ budget := by unfold allowance at hb; omega
  rw [execute]
  apply (bind_eq_some _ _ _ _).mpr
  refine ⟨(left.toList, right.toList), budget - conversionCharge left right,
    congrArg Prod.fst (BudgetedSeparatorCall.complete _ _ _ hc), ?_⟩
  have h := BudgetedSeparatorCheck.execute_complete capacity target blocks left.toList right.toList
    left.size right.size (budget - conversionCharge left right) (by simp) (by simp)
    (by unfold allowance at hb; omega)
  simpa only [allowance, Nat.sub_sub] using h

theorem value (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (blocks : List (Block n g)) (left right : Array (StoredEntry n))
    (budget : ℕ) (result : Bool) (remaining : ℕ)
    (h : (execute capacity target blocks left right budget).1 = some (result, remaining)) :
    result = (SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
      (blocks.map Block.source) left.toList right.toList).accepted := by
  obtain ⟨lists, rest, hp, ho⟩ := (bind_eq_some _ _ _ _).mp h
  obtain ⟨rfl, _, _⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hp
  exact (BudgetedSeparatorCheck.execute_value capacity target blocks left.toList right.toList
    left.size right.size rest (by simp) (by simp) result remaining ho).trans
      (BudgetedSeparatorCheck.reference_value capacity hcap target blocks left.toList right.toList)

theorem remaining (capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (left right : Array (StoredEntry n)) (budget : ℕ) (result : Bool) (rest : ℕ)
    (h : (execute capacity target blocks left right budget).1 = some (result, rest)) :
    budget = rest + allowance capacity target blocks left right := by
  obtain ⟨lists, rem, hp, ho⟩ := (bind_eq_some _ _ _ _).mp h
  obtain ⟨rfl, hrem, hcharge⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hp
  have hc := BudgetedSeparatorCheck.remaining capacity target blocks left.toList right.toList
    left.size right.size rem (by simp) (by simp) result rest ho
  unfold allowance
  omega


theorem allowance_scale (I : Instance n) (hn : 10000 ≤ n)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (blocks : List (Block n g)) (hlen : blocks.length = 4)
    (hg : g ≤ n) (hs : ∀ b ∈ blocks, b.steps ≤ n + 4)
    (left right : Array (StoredEntry n)) :
    allowance capacity target blocks left right ≤ inputScale I ^ 6 *
      ((SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
        (blocks.map Block.source) left.toList right.toList).scans + left.size + right.size + 1) := by
  let T := (SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
    (blocks.map Block.source) left.toList right.toList).scans + left.size + right.size + 1
  have hw := BudgetedSeparatorCheck.reference_work capacity hcap target blocks left.toList right.toList
  have hf := BudgetedSeparatorCheck.factor_scale I hn blocks hlen hg hs
  simp only [Array.length_toList] at hw
  have hcost : (BudgetedSeparatorCheck.reference capacity target blocks left.toList right.toList).2 ≤
      inputScale I ^ 5 * T := hw.trans (Nat.mul_le_mul_right T hf)
  have hconv : conversionCharge left right ≤ 5 * T := by
    unfold conversionCharge T
    omega
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hpow : 5 ≤ inputScale I ^ 5 :=
    (show 5 ≤ inputScale I by omega).trans (Nat.le_self_pow (by decide) _)
  have hc : inputScale I ^ 5 + 5 ≤ inputScale I ^ 6 := by
    calc
      inputScale I ^ 5 + 5 ≤ 2 * inputScale I ^ 5 := by omega
      _ ≤ inputScale I * inputScale I ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = inputScale I ^ 6 := by ring
  change conversionCharge left right + _ ≤ inputScale I ^ 6 * T
  calc
    _ ≤ (inputScale I ^ 5 + 5) * T := by nlinarith only [hcost, hconv]
    _ ≤ inputScale I ^ 6 * T := Nat.mul_le_mul_right T hc

end LowSpaceSubsetSum.BudgetedSeparatorArrays

end OAI
