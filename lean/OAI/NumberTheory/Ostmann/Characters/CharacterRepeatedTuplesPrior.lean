import OAI.NumberTheory.Ostmann.Characters.ShellPrior
import OAI.NumberTheory.Ostmann.Characters.WordSelection
import OAI.NumberTheory.Ostmann.Construction.DistinctValueWeights
import OAI.NumberTheory.Ostmann.Construction.RepeatedPhysical

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction Preliminaries

def characterTuplePrior {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) : FinitePrior (Fin b → PrimeUpTo Q) :=
  productPrior (fun i => primeShellPrior (E i) (hE i))

def characterTupleProduct {Q b : ℕ} (w : Fin b → PrimeUpTo Q) : ℕ := ∏ i, (w i).val

def characterTuplePeriod {Q b : ℕ} (w : Fin b → PrimeUpTo Q) : ℕ :=
  ∏ q : ↥(tupleDistinctPrimes (fun i => (w i).val)), (q : ℕ)

lemma characterTupleProduct_pos {Q b : ℕ} (w : Fin b → PrimeUpTo Q) :
    0 < characterTupleProduct w := Finset.prod_pos (fun i _ => (primeUpTo_prime (w i)).pos)

lemma characterTuplePeriod_pos {Q b : ℕ} (w : Fin b → PrimeUpTo Q) :
    0 < characterTuplePeriod w := Finset.prod_pos (fun q _ =>
      (tupleDistinctPrimes_prime _ (fun i => primeUpTo_prime (w i)) q).pos)

lemma characterTuplePrior_mass_eq_zero {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) (w : Fin b → PrimeUpTo Q)
    (hw : ¬ ∀ i, w i ∈ E i) : (characterTuplePrior E hE).mass w = 0 := by
  classical
  obtain ⟨i,hi⟩ := not_forall.mp hw
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [primeShellPrior_mass, ite_eq_right hi, zero_div]

lemma characterTuplePrior_mass_le {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) (w : Fin b → PrimeUpTo Q) :
    (characterTuplePrior E hE).mass w ≤
      (∏ i, (primeShellMass (E i))⁻¹)/(characterTupleProduct w : ℝ) := by
  classical
  change (∏ i, (primeShellPrior (E i) (hE i)).mass (w i)) ≤ _
  rw [characterTupleProduct, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod₀ (fun i _ => (primeShellPrior (E i) (hE i)).mass_nonneg _)
  intro i hi
  rw [primeShellPrior_mass]
  by_cases hw : w i ∈ E i
  · rw [ite_eq_left hw]
    simp [div_eq_mul_inv, mul_comm]
  · rw [ite_eq_right hw, zero_div]
    exact div_nonneg (inv_nonneg.mpr (hE i).le) (Nat.cast_nonneg _)

lemma characterTuple_reciprocal_period {Q b : ℕ} (w : Fin b → PrimeUpTo Q) :
    (∏ q ∈ tupleImage b w, (q.val : ℝ)⁻¹) = 1/(characterTuplePeriod w : ℝ) := by
  classical
  have he : (tupleImage b w).image Subtype.val = tupleDistinctPrimes (fun i => (w i).val) := by
    simp only [tupleImage, tupleDistinctPrimes, Finset.image_image, Function.comp_def]
  have hp := Finset.prod_image (s := tupleImage b w)
    (f := fun q : ℕ => (q : ℝ)⁻¹) (g := Subtype.val)
    (fun a _ b _ h => Subtype.ext h)
  rw [he] at hp
  rw [← hp, Finset.prod_inv_distrib]
  simp only [characterTuplePeriod, one_div, Finset.prod_coe_sort, Nat.cast_prod]

theorem characterTuple_supported_reciprocal_sum_le {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) :
    (∑ w : Fin b → PrimeUpTo Q,
      if ∀ i, w i ∈ E i then 1/(characterTuplePeriod w : ℝ) else 0) ≤
      (b : ℝ)^b*Real.exp (primeShellMass (Finset.univ.biUnion E)) := by
  classical
  let U := Finset.univ.biUnion E
  let f : PrimeUpTo Q → ℝ := fun p => if p ∈ U then (p.val : ℝ)⁻¹ else 0
  have hf : ∀ p, 0 ≤ f p := by intro p; dsimp [f]; split_ifs <;> positivity
  have hpoint (w : Fin b → PrimeUpTo Q) :
      (if ∀ i, w i ∈ E i then 1/(characterTuplePeriod w : ℝ) else 0) ≤
        ∏ p ∈ tupleImage b w, f p := by
    by_cases hw : ∀ i, w i ∈ E i
    · rw [ite_eq_left hw, ← characterTuple_reciprocal_period]
      apply le_of_eq
      apply Finset.prod_congr rfl
      intro p hp
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
      exact (ite_eq_left (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hw i⟩)).symm
    · rw [ite_eq_right hw]
      exact Finset.prod_nonneg (fun p _ => hf p)
  apply (Finset.sum_le_sum (fun w _ => hpoint w)).trans
  have hh := tuple_distinct_weight_sum_le b f hf
  simpa only [f, Finset.sum_ite_mem, Finset.univ_inter, primeShellMass, U] using hh

end Ostmann.Characters

end

end OAI
