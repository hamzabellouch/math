import OAI.NumberTheory.TwoPoint.Walks.TupleSlice
import OAI.NumberTheory.TwoPoint.Bounds.LiouvilleDivisorExtraction

namespace OAI

/-! The exact expansion indexed by the set of prime supplies replaced by
reciprocal constants. The original tuple and all progression tests are retained. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma indexed_indicator_product {J : ℕ} (p : Fin J → ℕ)
    (hprime : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (I : Finset (Fin J)) (n : ℕ) :
    (∏ i ∈ I, natDivisibilityIndicator (p i) n) =
      natDivisibilityIndicator (∏ i ∈ I, p i) n := by
  have hi : ∀ i ∈ I, ∀ j ∈ I, p i = p j → i = j := fun _ _ _ _ he => hinj he
  have hp : ∀ r ∈ I.image p, r.Prime := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := mem_image.mp hr
    exact hprime i
  calc
    _ = ∏ r ∈ I.image p, natDivisibilityIndicator r n := (prod_image hi).symm
    _ = natDivisibilityIndicator (∏ r ∈ I.image p, r) n :=
      natDivisibilityIndicator_product _ hp n
    _ = _ := by rw [prod_image hi]

lemma tupleCenter_expansion {J : ℕ} (p : Fin J → ℕ)
    (hprime : ∀ j, (p j).Prime) (hinj : Function.Injective p) (n : ℕ) :
    (∏ j, (natDivisibilityIndicator (p j) n - 1 / (p j : ℂ))) =
      ∑ I ∈ (univ : Finset (Fin J)).powerset,
        ((-1 : ℂ) ^ I.card / ((∏ i : I, p i : ℕ) : ℂ)) *
          natDivisibilityIndicator (∏ j : {j // j ∉ I}, p j) n := by
  rw [prod_sub]
  apply sum_congr rfl
  intro I _
  rw [indexed_indicator_product p hprime hinj (univ \ I) n]
  have hI : (∏ i ∈ I, p i) = ∏ i : I, p i := prod_subtype I (by simp) p
  have hc : (∏ j ∈ univ \ I, p j) = ∏ j : {j // j ∉ I}, p j :=
    prod_subtype (univ \ I) (by simp) p
  rw [hc, prod_div_distrib]
  simp only [prod_const_one, ← Nat.cast_prod, hI]
  ring

lemma tupleCenter_expansion_zero {J : ℕ} (p : Fin J → ℕ) (n : ℕ) :
    ((-1 : ℂ) ^ (∅ : Finset (Fin J)).card /
      ((∏ i : (∅ : Finset (Fin J)), p i : ℕ) : ℂ)) *
        natDivisibilityIndicator (∏ j : {j // j ∉ (∅ : Finset (Fin J))}, p j) n =
      natDivisibilityIndicator (∏ j, p j) n := by
  have he : (∏ j : {j // j ∉ (∅ : Finset (Fin J))}, p j) = ∏ j, p j := by
    exact (prod_subtype univ (by simp) p).symm
  simp only [card_empty, pow_zero, Fintype.prod_empty, Nat.cast_one, div_one, one_mul, he]

lemma tupleCenter_nonraw_expansion {J : ℕ} (p : Fin J → ℕ)
    (hprime : ∀ j, (p j).Prime) (hinj : Function.Injective p) (n : ℕ) :
    (∏ j, (natDivisibilityIndicator (p j) n - 1 / (p j : ℂ))) -
        natDivisibilityIndicator (∏ j, p j) n =
      ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        ((-1 : ℂ) ^ I.card / ((∏ i : I, p i : ℕ) : ℂ)) *
          natDivisibilityIndicator (∏ j : {j // j ∉ I}, p j) n := by
  let F := fun I : Finset (Fin J) =>
    ((-1 : ℂ) ^ I.card / ((∏ i : I, p i : ℕ) : ℂ)) *
      natDivisibilityIndicator (∏ j : {j // j ∉ I}, p j) n
  have hfilter : (univ : Finset (Fin J)).powerset.filter Finset.Nonempty =
      (univ : Finset (Fin J)).powerset.erase ∅ := by
    ext I
    simp only [mem_filter, mem_erase, nonempty_iff_ne_empty]
    exact and_comm
  rw [tupleCenter_expansion p hprime hinj n, hfilter]
  change (∑ I ∈ (univ : Finset (Fin J)).powerset, F I) - _ =
    ∑ I ∈ (univ : Finset (Fin J)).powerset.erase ∅, F I
  rw [← sum_erase_add _ F (empty_mem_powerset _)]
  have he : F ∅ = natDivisibilityIndicator (∏ j, p j) n := tupleCenter_expansion_zero p n
  rw [he]
  ring

lemma centeredTuple_nat_eq {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (x : (j : Fin J) → P j) (n : ℕ) :
    (centeredTuple (∏ j, (x j).val).primeFactors (n : ℤ) : ℂ) =
      ∏ j, (natDivisibilityIndicator (x j).val n - 1 / ((x j).val : ℂ)) := by
  have he : familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) x (n : ℤ) =
      centeredTuple (∏ j, (x j).val).primeFactors (n : ℤ) := by
    simpa only [familyTuple] using familyCenter_zero_eq_centeredTuple
      (fun j (p : P j) => p.val) (fun j p => hprime j _ p.property) x
      (selectedPrimeValues_injective x hdisjoint) (n : ℤ)
  rw [← he]
  simp only [familyCenter, zero_add, Complex.ofReal_prod, Complex.ofReal_sub,
    Complex.ofReal_inv, Complex.ofReal_natCast, natDivisibilityIndicator, one_div,
    Int.natCast_dvd_natCast]
  apply prod_congr rfl
  intro j _
  split_ifs <;> simp

end TwoPointCorrelations

end OAI
