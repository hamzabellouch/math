import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedConcretePrefix
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBucketProgram

namespace OAI

/-! # Retaining one left dictionary during the guarded right-prefix search -/

namespace LowSpaceSubsetSum.BudgetedBucket

open BudgetedSeparatorFlow

variable {n g : ℕ}

def run (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs)
    (B : ℕ)
    (check : Array (StoredEntry n) → Array (StoredEntry n) → ℕ →
      Option (Bool × ℕ) × ℕ) (budget : ℕ) :=
  bind (BudgetedSeparatorCall.run 8 (fun _ => ((), 7)) budget) fun _ rest =>
    bind (BudgetedParentCollector.collect D.left FL hFL B D.left.capacity
      StoredRestriction.empty rest) fun left available =>
      if left.val.keys.overflow || left.val.records.isEmpty then
        BudgetedSeparatorFlow.pure false available
      else BudgetedConcretePrefix.run D.right FR hFR B (check left.val.records)
        D.topOrder StoredRestriction.empty available

theorem value (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs)
    (hleft : D.left.maskRestriction = MaskRestriction.empty) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin g)))
    (check : Array (StoredEntry n) → Array (StoredEntry n) → ℕ →
      Option (Bool × ℕ) × ℕ)
    (hc : ∀ a b budget v rest, (check a b budget).1 = some (v, rest) →
      v = D.check families (a.map StoredEntry.semantic) (b.map StoredEntry.semantic) ∧
        rest ≤ budget)
    (budget : ℕ) (v : Bool) (rest : ℕ)
    (h : (run D FL FR hFL hFR B check budget).1 = some (v, rest)) :
    v = D.run B families ∧ rest ≤ budget := by
  obtain ⟨tag, first, hfirst, hnext⟩ := (bind_eq_some _ _ _ _).mp h
  obtain ⟨_, hf, _⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hfirst
  obtain ⟨left, available, hl, hr⟩ := (bind_eq_some _ _ _ _).mp hnext
  obtain ⟨hlvalue, hla⟩ := BudgetedParentCollector.value D.left FL hFL B D.left.capacity
    StoredRestriction.empty first left available hl
  have he := ComputedParentExecution.dictionary_value D.left FL StoredRestriction.empty hFL B
  have hreset : {D.left with maskRestriction := MaskRestriction.empty} = D.left := by
    rw [← hleft]
  rw [← hlvalue] at he
  change StoredEntry.mapDictionary left.val = _ at he
  change StoredEntry.mapDictionary left.val =
    ({D.left with maskRestriction := MaskRestriction.empty}.collect B).state.user at he
  rw [hreset] at he
  have hk := congrArg RecordedDictionary.State.keys he
  have hrecords := congrArg RecordedDictionary.State.records he
  change left.val.keys = _ at hk
  change left.val.records.map StoredEntry.semantic = _ at hrecords
  split at hr
  · simp only [BudgetedSeparatorFlow.pure, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl⟩
    constructor
    · rename_i hs
      simp only [Bool.or_eq_true] at hs
      dsimp only [RepresentationBucketData.run]
      rcases hs with ho | he
      · simp only [← hk, ho, ↓reduceIte]
      · have hi : (D.left.collect B).state.user.records.isEmpty = true := by
          rw [← hrecords]
          simpa only [Array.isEmpty, Array.size_map] using he
        simp only [hi, ↓reduceIte, ite_self]
    · omega
  · have hv := BudgetedConcretePrefix.value D.right FR hFR B (check left.val.records)
      (fun a => (D.check families (left.val.records.map StoredEntry.semantic)
        (a.map StoredEntry.semantic), 0))
      (D.check families (left.val.records.map StoredEntry.semantic))
      (hc left.val.records) (fun _ => rfl) D.topOrder StoredRestriction.empty available v rest hr
    constructor
    · rename_i hs
      have ho : left.val.keys.overflow = false := by
        cases hbool : left.val.keys.overflow <;> simp_all only [Bool.true_or, not_true_eq_false]
      have hi : left.val.records.isEmpty = false := by
        rw [ho, Bool.false_or] at hs
        exact Bool.eq_false_iff.mpr hs
      have himap : (left.val.records.map StoredEntry.semantic).isEmpty = false := by
        simpa only [Array.isEmpty, Array.size_map] using hi
      dsimp only [RepresentationBucketData.run]
      rw [← hk, ho, ← hrecords]
      simpa only [himap, Bool.false_eq_true, ↓reduceIte,
        StoredRestriction.empty_value] using hv.1
    · omega

theorem account (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs)
    (B : ℕ)
    (check : Array (StoredEntry n) → Array (StoredEntry n) → ℕ →
      Option (Bool × ℕ) × ℕ)
    (hc : ∀ a b budget, Account budget (check a b budget))
    (hn : 10000 ≤ n)
    (hll : ∀ j, (D.left.pair j).left.occurrences.card ≤ D.left.capacity)
    (hlr : ∀ j, (D.left.pair j).right.occurrences.card ≤ D.left.capacity)
    (hrl : ∀ j, (D.right.pair j).left.occurrences.card ≤ D.right.capacity)
    (hrr : ∀ j, (D.right.pair j).right.occurrences.card ≤ D.right.capacity)
    (hCL : D.left.capacity ≤ 2 ^ n) (hCR : D.right.capacity ≤ 2 ^ n)
    (hcopyL : (12 * n + 32) * 2 ^
      (Nat.clog 2 ({D.left with maskRestriction := StoredRestriction.empty.semantic}.pair 1).leftArray.size + 1) ≤ B)
    (hcopyR : ∀ P : StoredRestriction n, (12 * n + 32) *
      2 ^ (Nat.clog 2 ({D.right with maskRestriction := P.semantic}.pair 1).leftArray.size + 1) ≤ B)
    (budget : ℕ) : Account budget (run D FL FR hFL hFR B check budget) := by
  apply bind_account
  · exact ⟨BudgetedSeparatorCall.work _ _ _ (by decide),
      fun v left h => BudgetedSeparatorCall.spent _ _ _ (by decide) v left h⟩
  · intro tag rest h
    apply bind_account
    · exact BudgetedParentCollector.account D.left FL hFL B D.left.capacity
        StoredRestriction.empty rest hn hll hlr hCL hcopyL
    · intro left available hl
      split
      · exact pure_account false available
      · exact BudgetedConcretePrefix.account D.right FR hFR B (check left.val.records)
          (hc left.val.records) hn hrl hrr hCR hcopyR D.topOrder StoredRestriction.empty available

noncomputable def allowance (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs) (B : ℕ)
    (checkBill : Array (StoredEntry n) → Array (StoredEntry n) → ℕ) : ℕ :=
  let left := (ComputedParentExecution.run D.left FL StoredRestriction.empty hFL B).1.dictionary
  8 + BudgetedParentCollector.bill D.left B D.left.capacity StoredRestriction.empty +
    if left.val.keys.overflow || left.val.records.isEmpty then 0 else
      BudgetedConcretePrefix.allowance D.right FR hFR B (checkBill left.val.records)
        D.topOrder StoredRestriction.empty

theorem complete (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs) (B : ℕ)
    (check : Array (StoredEntry n) → Array (StoredEntry n) → ℕ →
      Option (Bool × ℕ) × ℕ)
    (checkBill : Array (StoredEntry n) → Array (StoredEntry n) → ℕ)
    (hc : ∀ a b budget, checkBill a b ≤ budget →
      ∃ v rest, (check a b budget).1 = some (v, rest))
    (hr : ∀ a b budget v rest, (check a b budget).1 = some (v, rest) →
      budget ≤ rest + checkBill a b)
    (hn : 10000 ≤ n) (budget : ℕ)
    (hb : allowance D FL FR hFL hFR B checkBill ≤ budget) :
    ∃ v rest, (run D FL FR hFL hFR B check budget).1 = some (v, rest) := by
  have hhead : 8 ≤ budget := by dsimp only [allowance] at hb; omega
  have hbill : BudgetedParentCollector.bill D.left B D.left.capacity
      StoredRestriction.empty ≤ budget - 8 := by
    dsimp only [allowance] at hb
    omega
  obtain ⟨available, hl⟩ := BudgetedParentCollector.complete D.left FL hFL B D.left.capacity
    StoredRestriction.empty (budget - 8) hn hbill
  have hrem := BudgetedParentCollector.remaining D.left FL hFL B D.left.capacity
    StoredRestriction.empty (budget - 8) hn _ available hl
  rw [run]
  have hh := congrArg Prod.fst (BudgetedSeparatorCall.complete 8 (fun _ => ((), 7)) budget hhead)
  simp only [BudgetedSeparatorFlow.bind, hh, hl]
  split
  · exact ⟨false, available, rfl⟩
  · have hp : BudgetedConcretePrefix.allowance D.right FR hFR B
        (checkBill (ComputedParentExecution.run D.left FL StoredRestriction.empty hFL B).1.dictionary.val.records)
        D.topOrder StoredRestriction.empty ≤ available := by
      dsimp only [allowance] at hb
      split at hb
      · contradiction
      · omega
    exact BudgetedConcretePrefix.complete D.right FR hFR B _ _ (hc _) (hr _)
      hn D.topOrder StoredRestriction.empty available hp

theorem remaining (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs) (B : ℕ)
    (check : Array (StoredEntry n) → Array (StoredEntry n) → ℕ →
      Option (Bool × ℕ) × ℕ)
    (checkBill : Array (StoredEntry n) → Array (StoredEntry n) → ℕ)
    (hr : ∀ a b budget v rest, (check a b budget).1 = some (v, rest) →
      budget ≤ rest + checkBill a b)
    (hn : 10000 ≤ n) (budget : ℕ) (v : Bool) (rest : ℕ)
    (h : (run D FL FR hFL hFR B check budget).1 = some (v, rest)) :
    budget ≤ rest + allowance D FL FR hFL hFR B checkBill := by
  obtain ⟨tag, first, hfirst, hnext⟩ := (bind_eq_some _ _ _ _).mp h
  obtain ⟨_, hf, hh⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hfirst
  obtain ⟨left, available, hl, hp⟩ := (bind_eq_some _ _ _ _).mp hnext
  have hlv := (BudgetedParentCollector.value D.left FL hFL B D.left.capacity
    StoredRestriction.empty first left available hl).1
  have hlr := BudgetedParentCollector.remaining D.left FL hFL B D.left.capacity
    StoredRestriction.empty first hn left available hl
  dsimp only [allowance]
  rw [← hlv]
  split at hp
  next hs =>
    simp only [BudgetedSeparatorFlow.pure, Option.some.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩
    rw [ite_eq_left hs]
    omega
  next hs =>
    rw [ite_eq_right hs]
    have hpr := BudgetedConcretePrefix.remaining D.right FR hFR B (check left.val.records)
      (checkBill left.val.records) (hr left.val.records) hn D.topOrder
      StoredRestriction.empty available v rest hp
    omega

end LowSpaceSubsetSum.BudgetedBucket

end OAI
