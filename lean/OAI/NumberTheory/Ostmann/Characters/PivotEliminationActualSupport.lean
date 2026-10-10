import OAI.NumberTheory.Ostmann.Characters.PivotEliminationRange
import OAI.NumberTheory.Ostmann.Characters.PivotProductFibers

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.PivotEliminationActual
open Construction Preliminaries PivotProductFibers
open scoped BigOperators

def positiveTupleProduct {Q n : ℕ} (w : PrimeTuple Q n) : ℕ+ :=
  ⟨tupleProduct w, tupleProduct_pos w⟩

@[simp] theorem coe_positiveTupleProduct {Q n : ℕ} (w : PrimeTuple Q n) :
    (positiveTupleProduct w : ℕ) = tupleProduct w := rfl

def positiveProductRange {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q)) : Finset ℕ+ := by
  classical
  exact (Finset.univ.filter fun w : PrimeTuple Q n => ∀ i, w i ∈ E i).image positiveTupleProduct

@[simp] theorem mem_positiveProductRange {Q n : ℕ}
    (E : Fin n → Finset (PrimeUpTo Q)) (P : ℕ+) :
    P ∈ positiveProductRange E ↔
      ∃ w : PrimeTuple Q n, (∀ i, w i ∈ E i) ∧ positiveTupleProduct w = P := by
  classical
  simp [positiveProductRange]

theorem tuple_supported_of_mass_ne_zero {Q n : ℕ}
    (E : Fin n → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (w : PrimeTuple Q n) (hw : (characterTuplePrior E hE).mass w ≠ 0) :
    ∀ i, w i ∈ E i := by
  by_contra h
  exact hw (characterTuplePrior_mass_eq_zero E hE w h)

theorem product_mem_range_of_mass_ne_zero {Q n : ℕ}
    (E : Fin n → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (w : PrimeTuple Q n) (hw : (characterTuplePrior E hE).mass w ≠ 0) :
    positiveTupleProduct w ∈ positiveProductRange E :=
  (mem_positiveProductRange E _).mpr ⟨w, tuple_supported_of_mass_ne_zero E hE w hw, rfl⟩

theorem fiber_mass_mul_residue_card_le {Q n : ℕ}
    (E : Fin n → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i)) (P : ℕ+) :
    (∑ w : PrimeTuple Q n with positiveTupleProduct w = P, (characterTuplePrior E hE).mass w) *
      (Fintype.card (ZMod (P : ℕ)) : ℝ) ≤ (n.factorial : ℝ) * normalization E := by
  classical
  have he : (Finset.univ.filter fun w : PrimeTuple Q n => positiveTupleProduct w = P) =
      productFiber Q n P := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_productFiber]
    exact Subtype.ext_iff
  rw [he, ZMod.card]
  have hh := mul_le_mul_of_nonneg_right (productFiber_mass_le E hE (P : ℕ))
    (show (0 : ℝ) ≤ (P : ℕ) by positivity)
  have hP : ((P : ℕ) : ℝ) ≠ 0 := by exact_mod_cast P.ne_zero
  simpa only [div_mul_cancel₀ _ hP, characterTuplePrior] using hh

end Ostmann.Characters.PivotEliminationActual

end

end OAI
