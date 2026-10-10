import OAI.NumberTheory.TwoPoint.Walks.TupleSlice
import OAI.NumberTheory.TwoPoint.Bounds.MertensScale
import OAI.NumberTheory.TwoPoint.Bounds.RoughSieveProbability

namespace OAI

/-! Arithmetic support and mass of the removed and retained tuple supplies. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma prime_dvd_primeTupleSlice {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime) {z p : ℕ}
    (hz : z ∈ primeTupleSlice P I) (hp : p.Prime) (hd : p ∣ z) :
    ∃ i ∈ I, p ∈ P i := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hz
  obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff (fun i : I => (x i).val)).mp hd
  have he : p = (x i).val := (Nat.prime_dvd_prime_iff_eq hp
    (hprime i _ (x i).property)).mp hi
  exact ⟨i, i.property, he.symm ▸ (x i).property⟩

lemma primeTupleSlice_avoids {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime) (y : ℝ) (hy : 0 ≤ y)
    (hlarge : ∀ i, ∀ p ∈ P i, y < (p : ℝ)) {z : ℕ}
    (hz : z ∈ primeTupleSlice P I) : avoidsPrimeSet (sievePrimesUpTo y) z := by
  intro p hp hd
  obtain ⟨i, _, hi⟩ := prime_dvd_primeTupleSlice P I hprime hz
    (sievePrimesUpTo_prime y p hp) hd
  exact (not_lt_of_ge (sievePrimesUpTo_le y hy p hp)) (hlarge i p hi)

lemma primeTupleSlice_le_full_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hne : ∀ i, (P i).Nonempty) (B : ℝ)
    (hB : ∀ d ∈ primeTupleDivisors P, (d : ℝ) ≤ B)
    {z : ℕ} (hz : z ∈ primeTupleSlice P I) : (z : ℝ) ≤ B := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hz
  let x' : (j : Fin J) → P j := fun j =>
    if hj : j ∈ I then x ⟨j, hj⟩ else ⟨(hne j).choose, (hne j).choose_spec⟩
  have he : (∏ i : I, (x i).val) = ∏ i : I, (x' i).val := by
    apply prod_congr rfl
    intro i _
    simp only [x', dite_eq_left i.property]
  have hd : (∏ i : I, (x i).val) ∣ ∏ j, (x' j).val := by
    rw [he, prod_coe_sort I (fun j : Fin J => (x' j).val)]
    exact prod_dvd_prod_of_subset I univ (fun j => (x' j).val) (subset_univ I)
  have hpos : 0 < ∏ j, (x' j).val := prod_pos fun j _ => (hprime j _ (x' j).property).pos
  have hle : (∏ i : I, (x i).val) ≤ ∏ j, (x' j).val := Nat.le_of_dvd hpos hd
  exact (show ((∏ i : I, (x i).val : ℕ) : ℝ) ≤ (∏ j, (x' j).val : ℕ) by
    exact_mod_cast hle).trans (hB _ (mem_image.mpr ⟨x', mem_univ _, rfl⟩))

lemma primeTupleSlice_mass_le_full {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j))
    (hmass : ∀ i, 1 ≤ primeHarmonicMass (P i)) :
    (∑ z ∈ primeTupleSlice P I, 1 / (z : ℝ)) ≤ ∏ i, primeHarmonicMass (P i) := by
  rw [primeTupleSlice_mass P I hprime hdisjoint,
    prod_coe_sort I (fun j : Fin J => primeHarmonicMass (P j))]
  exact prod_le_prod_of_subset_of_one_le₀ (subset_univ I)
    (fun i _ => zero_le_one.trans (hmass i)) (fun i _ _ => hmass i)

lemma retainedTuple_le_full_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hne : ∀ i, (P i).Nonempty) (B : ℝ)
    (hB : ∀ d ∈ primeTupleDivisors P, (d : ℝ) ≤ B)
    (y : (j : {j // j ∉ I}) → P j) : (∏ j, (y j).val : ℕ) ≤ B := by
  let x : (j : Fin J) → P j := fun j =>
    if hj : j ∉ I then y ⟨j, hj⟩ else ⟨(hne j).choose, (hne j).choose_spec⟩
  have he : (∏ j, (y j).val) = ∏ j : {j // j ∉ I}, (x j).val := by
    apply prod_congr rfl
    intro j _
    simp only [x, dite_eq_left j.property]
  have hs := (prod_subtype (p := fun j : Fin J => j ∉ I) (F := inferInstance) (univ \ I) (by simp) (fun j : Fin J => (x j).val)).symm
  have hd : (∏ j, (y j).val) ∣ ∏ j, (x j).val := by
    rw [he, hs]
    exact prod_dvd_prod_of_subset (univ \ I) univ (fun j => (x j).val) (subset_univ _)
  have hpos : 0 < ∏ j, (x j).val := prod_pos fun j _ => (hprime j _ (x j).property).pos
  have hle := Nat.le_of_dvd hpos hd
  exact (show ((∏ j, (y j).val : ℕ) : ℝ) ≤ (∏ j, (x j).val : ℕ) by
    exact_mod_cast hle).trans (hB _ (mem_image.mpr ⟨x, mem_univ _, rfl⟩))

end TwoPointCorrelations

end OAI
