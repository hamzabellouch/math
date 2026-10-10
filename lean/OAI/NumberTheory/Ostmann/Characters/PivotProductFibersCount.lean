import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Factors
import OAI.NumberTheory.Ostmann.Characters.ShellPrior

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.PivotProductFibers
open Construction Preliminaries

abbrev PrimeTuple (Q n : ℕ) := Fin n → PrimeUpTo Q

def tupleProduct {Q n : ℕ} (w : PrimeTuple Q n) : ℕ := ∏i,(w i).val

def tupleList {Q n : ℕ} (w : PrimeTuple Q n) : List ℕ := List.ofFn (fun i => (w i).val)

def productFiber (Q n P : ℕ) : Finset (PrimeTuple Q n) :=
  Finset.univ.filter (fun w => tupleProduct w=P)

@[simp] theorem mem_productFiber {Q n P : ℕ} {w : PrimeTuple Q n} :
    w ∈ productFiber Q n P ↔ tupleProduct w=P := by
  simp only [productFiber,Finset.mem_filter,Finset.mem_univ,true_and]

theorem tupleProduct_pos {Q n : ℕ} (w : PrimeTuple Q n) : 0 < tupleProduct w :=
  Finset.prod_pos (fun i _ => (primeUpTo_prime (w i)).pos)

theorem tupleList_injective (Q n : ℕ) : Function.Injective (@tupleList Q n) := by
  intro w v h
  have hv := List.ofFn_injective h
  funext i
  apply Subtype.ext
  exact congrFun hv i

theorem tupleList_perm_of_product_eq {Q n : ℕ} (w v : PrimeTuple Q n)
    (h : tupleProduct w=tupleProduct v) : (tupleList w).Perm (tupleList v) := by
  have hw : (tupleList w).Perm (Nat.primeFactorsList (tupleProduct w)) :=
    Nat.primeFactorsList_unique (by simp only [tupleList,List.prod_ofFn,tupleProduct]) (by
      intro p hp
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
      exact primeUpTo_prime (w i))
  have hv : (tupleList v).Perm (Nat.primeFactorsList (tupleProduct v)) :=
    Nat.primeFactorsList_unique (by simp only [tupleList,List.prod_ofFn,tupleProduct]) (by
      intro p hp
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
      exact primeUpTo_prime (v i))
  rw [h] at hw
  exact hw.trans hv.symm

theorem productFiber_card_le (Q n P : ℕ) : (productFiber Q n P).card ≤ n.factorial := by
  classical
  by_cases h : (productFiber Q n P).Nonempty
  · obtain ⟨w,hw⟩ := h
    have hcard : (productFiber Q n P).card ≤ ((tupleList w).permutations.toFinset).card := by
      apply Finset.card_le_card_of_injOn tupleList
      · intro v hv
        apply List.mem_toFinset.mpr
        apply List.mem_permutations.mpr
        exact tupleList_perm_of_product_eq v w
          ((mem_productFiber.mp hv).trans (mem_productFiber.mp hw).symm)
      · exact (tupleList_injective Q n).injOn
    apply hcard.trans
    have hp := List.toFinset_card_le (tupleList w).permutations
    simpa only [List.length_permutations,tupleList,List.length_ofFn] using hp
  · rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.card_empty]
    exact Nat.zero_le _

def distinctProductFiber (Q n P : ℕ) : Finset (PrimeTuple Q n) := by
  classical
  exact (productFiber Q n P).filter (fun w => Function.Injective (fun i => (w i).val))

theorem distinctProductFiber_subset (Q n P : ℕ) :
    distinctProductFiber Q n P ⊆ productFiber Q n P := Finset.filter_subset _ _

theorem distinctProductFiber_card_le (Q n P : ℕ) :
    (distinctProductFiber Q n P).card ≤ n.factorial :=
  (Finset.card_le_card (distinctProductFiber_subset Q n P)).trans (productFiber_card_le Q n P)

end Ostmann.Characters.PivotProductFibers

end

end OAI
