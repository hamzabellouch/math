import OAI.NumberTheory.TwoPoint.Walks.TupleColumnWords
import OAI.NumberTheory.TwoPoint.Bounds.PrimeFamilyWeights

namespace OAI

/-! Disjoint prime pools give the actual tuple factorization and unique tuple labels. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma selectedPrimeValues_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (x : (j : Fin J) → P j)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun j => (x j).val) := by
  intro j l he
  change (x j).val = (x l).val at he
  by_contra hne
  have hj : (x j).val ∈ P l := by rw [he]; exact (x l).property
  exact (disjoint_left.mp (hdisjoint j l (Ne.symm hne))) (x j).property hj

lemma columnTuple_primeFactors {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (columnTuple w i).primeFactors = univ.image (fun j => (w j i).val) := by
  exact familyTuple_primeFactors (fun _ p => p.val)
    (fun j p => hprime j _ p.property) (fun j => w j i)
    (selectedPrimeValues_injective (fun j => w j i) hdisjoint)

lemma columnTuple_primeFactors_card {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (columnTuple w i).primeFactors.card = J := by
  rw [columnTuple_primeFactors w i hprime hdisjoint,
    card_image_of_injective _ (selectedPrimeValues_injective (fun j => w j i) hdisjoint),
    card_univ, Fintype.card_fin]

lemma columnTuple_squarefree {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Squarefree (columnTuple w i) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro j _ l _ hne
    change IsRelPrime (w j i).val (w l i).val
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hprime j _ (w j i).property)
      (hprime l _ (w l i).property)).mpr
      (fun he => hne (selectedPrimeValues_injective (fun j => w j i) hdisjoint he))
  · intro j _
    exact (hprime j _ (w j i).property).squarefree

/-- The numerical whole tuple determines its column choices, as used by
the nonbacktracking matrix's actual copy labels. -/
theorem primeTuple_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun x : (j : Fin J) → P j => ∏ j, (x j).val) := by
  intro x y he
  change (∏ j, (x j).val) = (∏ j, (y j).val) at he
  funext j
  apply Subtype.ext
  have hp := hprime j _ (x j).property
  have hd : (x j).val ∣ ∏ l, (y l).val := by
    rw [← he]
    exact dvd_prod_of_mem (fun l => (x l).val) (mem_univ j)
  obtain ⟨l, _, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun l => (y l).val)).mp hd
  have hv : (x j).val = (y l).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime l _ (y l).property)).mp hdiv
  have hjl : j = l := by
    by_contra hne
    exact (disjoint_left.mp (hdisjoint j l (Ne.symm hne)))
      (x j).property (hv.symm ▸ (y l).property)
  subst l
  exact hv

end TwoPointCorrelations

end OAI
