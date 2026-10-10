import OAI.Combinatorics.EditApproximation.Binary.BinaryBandInputs
import OAI.Combinatorics.EditApproximation.Geometry.OnlineLinearBits
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The actual optimistic linear objective constructed from stored Boolean
fractions, using counted sums, products and divisions. No reduced-rational
conversion is used between the table inputs and the optimizer. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

@[simp] theorem canonicalAddWithWork_value (a b : BinaryFraction) :
    (canonicalAddWithWork a b).1.value = a.value + b.value := by
  rw [← representation_value, canonicalAddWithWork_representation,
    UnreducedRational.value_add, representation_value, representation_value]

@[simp] theorem canonicalMulWithWork_value (a b : BinaryFraction) :
    (canonicalMulWithWork a b).1.value = a.value * b.value := by
  rw [← representation_value, canonicalMulWithWork_representation,
    UnreducedRational.value_mul, representation_value, representation_value]

@[simp] theorem divWithWork_value (a b : BinaryFraction) :
    (divWithWork a b).1.value = a.value / b.value := by
  rw [← representation_value, divWithWork_representation,
    UnreducedRational.value_div, representation_value, representation_value]

@[simp] theorem subWithWork_value (a b : BinaryFraction) :
    (subWithWork a b).1.value = a.value - b.value := by
  rw [← representation_value, subWithWork_representation,
    UnreducedRational.value_sub, representation_value, representation_value]

def gainWithWork {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) : BinaryFraction × ℕ :=
  let quotient := divWithWork (table s i).neg (mass i.1)
  (quotient.1, quotient.2 + 1)

def decrementWithWork {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) : BinaryFraction × ℕ :=
  let difference := subWithWork (table s i) (table (s + 1) i)
  let quotient := divWithWork difference.1 (mass i.1)
  (quotient.1, difference.2 + quotient.2 + 1)



def optimisticTermWithWork {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) : BinaryFraction × ℕ :=
  let gain := gainWithWork mass table s i
  let decrement := decrementWithWork mass table s i
  let scaled := canonicalMulWithWork coefficient decrement.1
  let total := canonicalAddWithWork gain.1 scaled.1
  (total.1, gain.2 + decrement.2 + scaled.2 + total.2 + 2)

@[simp] theorem gainWithWork_value {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) :
    (gainWithWork mass table s i).1.value =
      childGain (fun j => (mass j).value) (fun t j => (table t j).value) s i := by
  simp only [gainWithWork, divWithWork_value, neg_value, childGain]

@[simp] theorem decrementWithWork_value {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) :
    (decrementWithWork mass table s i).1.value =
      childDecrement (fun j => (mass j).value) (fun t j => (table t j).value) s i := by
  simp only [decrementWithWork, divWithWork_value, subWithWork_value, childDecrement]

@[simp] theorem coefficientWithWork_value (kappa : BinaryFraction) :
    (coefficientWithWork kappa).1.value = 1 - 2 * kappa.value := by
  simp only [coefficientWithWork, subWithWork_value, canonicalMulWithWork_value]
  rw [← representation_value one, one_representation, UnreducedRational.value_one,
    ← representation_value (nat 2), nat_representation, UnreducedRational.value_nat]
  norm_num

def onlineLinearWithWork {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) : BinaryFraction × ℕ :=
  let coefficient := coefficientWithWork kappa
  let terms := vectorMapWithWork t fun s => optimisticTermWithWork mass table coefficient.1 s.val i
  let history := bandMassTotalWithWork terms.1
  let current := gainWithWork mass table t i
  let total := canonicalAddWithWork history.1 current.1
  let result := canonicalMulWithWork eta total.1
  (result.1, coefficient.2 + terms.2 + history.2 + current.2 + total.2 + result.2 + 3)

theorem onlineLinearWithWork_value {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) :
    (onlineLinearWithWork mass table eta kappa t i).1.value =
      rationalOnlineLinear eta.value kappa.value (childGain (fun j => (mass j).value)
        (fun s j => (table s j).value))
        (childDecrement (fun j => (mass j).value) (fun s j => (table s j).value)) t i := by
  simp only [onlineLinearWithWork, canonicalMulWithWork_value, canonicalAddWithWork_value,
    bandMassTotalWithWork_value, vectorMapWithWork_value, optimisticTermWithWork,
    coefficientWithWork_value, gainWithWork_value, decrementWithWork_value]
  unfold rationalOnlineLinear rationalOptimisticHistory
  congr 2
  exact Fin.sum_univ_eq_sum_range (fun s => childGain (fun j => (mass j).value)
    (fun s j => (table s j).value) s i + (1 - 2 * kappa.value) *
      childDecrement (fun j => (mass j).value) (fun s j => (table s j).value) s i) t

theorem gainWithWork_storage {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) (Bm Bt : ℕ)
    (hm : (mass i.1).width ≤ Bm) (ht : (table s i).width ≤ Bt) :
    (gainWithWork mass table s i).1.representation.storageBits ≤ 2 * Bt + 2 * Bm + 4 := by
  have hm' := representation_storageBits_le (mass i.1)
  have ht' := representation_storageBits_le (table s i)
  change (divWithWork (table s i).neg (mass i.1)).1.representation.storageBits ≤ _
  rw [divWithWork_representation, neg_representation]
  have h := UnreducedRational.storageBits_div (table s i).representation.neg (mass i.1).representation
  rw [UnreducedRational.storageBits_neg] at h
  omega

theorem decrementWithWork_storage {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) (Bm Bt : ℕ)
    (hm : (mass i.1).width ≤ Bm) (ht : (table s i).width ≤ Bt) (ht' : (table (s + 1) i).width ≤ Bt) :
    (decrementWithWork mass table s i).1.representation.storageBits ≤ 8 * Bt + 2 * Bm + 9 := by
  have hm' := representation_storageBits_le (mass i.1)
  have ho := representation_storageBits_le (table s i)
  have hn := representation_storageBits_le (table (s + 1) i)
  have hs := UnreducedRational.storageBits_sub (table s i).representation (table (s + 1) i).representation
  have hd := UnreducedRational.storageBits_div ((table s i).representation.sub (table (s + 1) i).representation) (mass i.1).representation
  change (divWithWork (subWithWork (table s i) (table (s + 1) i)).1 (mass i.1)).1.representation.storageBits ≤ _
  rw [divWithWork_representation, subWithWork_representation]
  omega

theorem coefficientWithWork_storage (kappa : BinaryFraction) (Bk : ℕ) (hk : kappa.width ≤ Bk) :
    (coefficientWithWork kappa).1.representation.storageBits ≤ 4 * Bk + 18 := by
  have hk' := representation_storageBits_le kappa
  have hm := UnreducedRational.storageBits_mul (UnreducedRational.nat 2) kappa.representation
  have hs := UnreducedRational.storageBits_sub UnreducedRational.one
    ((UnreducedRational.nat 2).mul kappa.representation)
  have htwo : (UnreducedRational.nat 2).storageBits = 4 := by decide
  rw [htwo] at hm
  rw [UnreducedRational.storageBits_one] at hs
  change (subWithWork one (canonicalMulWithWork (nat 2) kappa).1).1.representation.storageBits ≤ _
  rw [subWithWork_representation, one_representation, canonicalMulWithWork_representation, nat_representation]
  omega

def optimisticTermStorageBudget (Bm Bt Bc : ℕ) : ℕ := 20 * Bt + 8 * Bm + 4 * Bc + 30

theorem optimisticTermWithWork_storage {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) (Bm Bt Bc : ℕ)
    (hm : (mass i.1).width ≤ Bm) (ht : (table s i).width ≤ Bt)
    (ht' : (table (s + 1) i).width ≤ Bt) (hc : coefficient.width ≤ Bc) :
    (optimisticTermWithWork mass table coefficient s i).1.representation.storageBits ≤
      optimisticTermStorageBudget Bm Bt Bc := by
  have hg := gainWithWork_storage mass table s i Bm Bt hm ht
  have hd := decrementWithWork_storage mass table s i Bm Bt hm ht ht'
  have hc' := representation_storageBits_le coefficient
  have hp := UnreducedRational.storageBits_mul coefficient.representation
    (decrementWithWork mass table s i).1.representation
  have ha := UnreducedRational.storageBits_add (gainWithWork mass table s i).1.representation
    (coefficient.representation.mul (decrementWithWork mass table s i).1.representation)
  change (canonicalAddWithWork (gainWithWork mass table s i).1
    (canonicalMulWithWork coefficient (decrementWithWork mass table s i).1).1).1.representation.storageBits ≤ _
  rw [canonicalAddWithWork_representation, canonicalMulWithWork_representation]
  unfold optimisticTermStorageBudget
  omega

def onlineLinearStorageBudget (Be Bk Bm Bt t : ℕ) : ℕ :=
  2 * Be + 2 * bandMassTotalStorageBudget t (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) +
    2 * (2 * Bt + 2 * Bm + 4) + 3

theorem onlineLinearWithWork_storage {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) (Be Bk Bm Bt : ℕ)
    (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk) (hm : (mass i.1).width ≤ Bm)
    (ht : ∀ s ≤ t + 1, (table s i).width ≤ Bt) :
    (onlineLinearWithWork mass table eta kappa t i).1.width ≤
      onlineLinearStorageBudget Be Bk Bm Bt t := by
  let coefficient := (coefficientWithWork kappa).1
  let terms := (vectorMapWithWork t fun s => optimisticTermWithWork mass table coefficient s.val i).1
  let history := (bandMassTotalWithWork terms).1
  let current := (gainWithWork mass table t i).1
  have hcn := canonicalAddWithWork_self_width one (canonicalMulWithWork (nat 2) kappa).1.neg
  change coefficient.width ≤ coefficient.representation.storageBits at hcn
  have hc : coefficient.width ≤ 4 * Bk + 18 := hcn.trans (coefficientWithWork_storage kappa Bk hk)
  have hterms (s : Fin t) : (terms.get s).width ≤ optimisticTermStorageBudget Bm Bt (4 * Bk + 18) := by
    have hs := optimisticTermWithWork_storage mass table coefficient s.val i Bm Bt (4 * Bk + 18)
      hm (ht s.val (by omega)) (ht (s.val + 1) (by omega)) hc
    simp only [terms, vectorMapWithWork_value]
    exact (canonicalAddWithWork_self_width _ _).trans hs
  have hh := bandMassTotalWithWork_storage terms (optimisticTermStorageBudget Bm Bt (4 * Bk + 18)) hterms
  change history.representation.storageBits ≤ _ at hh
  have hg := gainWithWork_storage mass table t i Bm Bt hm (ht t (by omega))
  change current.representation.storageBits ≤ _ at hg
  have he' := representation_storageBits_le eta
  have ha := UnreducedRational.storageBits_add history.representation current.representation
  have hp := UnreducedRational.storageBits_mul eta.representation (history.representation.add current.representation)
  change (canonicalMulWithWork eta (canonicalAddWithWork history current).1).1.width ≤ _
  have hw := canonicalMulWithWork_self_width eta (canonicalAddWithWork history current).1
  rw [canonicalMulWithWork_representation, canonicalAddWithWork_representation] at hw
  unfold onlineLinearStorageBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
