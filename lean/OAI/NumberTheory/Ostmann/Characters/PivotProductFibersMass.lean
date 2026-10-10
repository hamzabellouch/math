import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesPrior
import OAI.NumberTheory.Ostmann.Characters.PivotProductFibersCount

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.PivotProductFibers
open Construction Preliminaries

def normalization {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q)) : ℝ :=
  ∏i,(primeShellMass (E i))⁻¹

theorem normalization_nonneg {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (hE : ∀i,0 < primeShellMass (E i)) : 0 ≤ normalization E :=
  Finset.prod_nonneg (fun i _ => (inv_pos.mpr (hE i)).le)

theorem tuple_mass_le {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (hE : ∀i,0 < primeShellMass (E i)) (w : PrimeTuple Q n) :
    (productPrior (fun i => primeShellPrior (E i) (hE i))).mass w ≤
      normalization E / (tupleProduct w : ℝ) :=
  characterTuplePrior_mass_le E hE w

theorem productFiber_mass_le {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (hE : ∀i,0 < primeShellMass (E i)) (P : ℕ) :
    (∑w∈productFiber Q n P,(productPrior (fun i => primeShellPrior (E i) (hE i))).mass w) ≤
      (n.factorial:ℝ) * normalization E / P := by
  calc
    _ ≤ ∑_w∈productFiber Q n P,normalization E/(P:ℝ) := by
      apply Finset.sum_le_sum
      intro w hw
      have hh := tuple_mass_le E hE w
      rw [mem_productFiber.mp hw] at hh
      exact hh
    _ = ((productFiber Q n P).card:ℝ)*(normalization E/(P:ℝ)) := by simp
    _ ≤ (n.factorial:ℝ)*(normalization E/(P:ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast productFiber_card_le Q n P)
        (div_nonneg (normalization_nonneg E hE) (Nat.cast_nonneg P))
    _ = _ := (mul_div_assoc _ _ _).symm

theorem distinctProductFiber_mass_le {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (hE : ∀i,0 < primeShellMass (E i)) (P : ℕ) :
    (∑w∈distinctProductFiber Q n P,
      (productPrior (fun i => primeShellPrior (E i) (hE i))).mass w) ≤
        (n.factorial:ℝ) * normalization E / P := by
  apply le_trans _ (productFiber_mass_le E hE P)
  apply Finset.sum_le_sum_of_subset_of_nonneg (distinctProductFiber_subset Q n P)
  intro w hw hn
  exact (productPrior (fun i => primeShellPrior (E i) (hE i))).mass_nonneg w

theorem distinct_product_indicator_mass_le {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (hE : ∀i,0 < primeShellMass (E i)) (P : ℕ) :
    (∑w : PrimeTuple Q n, if Function.Injective (fun i => (w i).val) ∧ tupleProduct w=P
      then (productPrior (fun i => primeShellPrior (E i) (hE i))).mass w else 0) ≤
        (n.factorial:ℝ) * (∏i,(primeShellMass (E i))⁻¹) / P := by
  classical
  have h := distinctProductFiber_mass_le E hE P
  simpa only [distinctProductFiber,productFiber,Finset.sum_filter,ite_and,
    normalization,and_comm] using h

end Ostmann.Characters.PivotProductFibers

end

end OAI
