import OAI.NumberTheory.TwoPoint.Walks.PartialTupleProfiles

namespace OAI

/-! The actual centered tuple average is the signed sum of the supply
subsets. The empty subset is precisely the full-divisibility term. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma tuple_center_padding_expansion {J : ℕ} (p : Fin J → ℕ)
    (hprime : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (q n : ℕ) (hcop : ∀ j, q.Coprime (p j)) (F : ℂ) :
    natDivisibilityIndicator q n *
        (∏ j, (natDivisibilityIndicator (p j) n - 1 / (p j : ℂ))) * F =
      ∑ I ∈ (univ : Finset (Fin J)).powerset,
        ((-1 : ℂ) ^ I.card / ((∏ i : I, p i : ℕ) : ℂ)) *
          natDivisibilityIndicator (q * ∏ j : {j // j ∉ I}, p j) n * F := by
  rw [tupleCenter_expansion p hprime hinj n, mul_sum, sum_mul]
  apply sum_congr rfl
  intro I _
  have hc : q.Coprime (∏ j : {j // j ∉ I}, p j) :=
    Nat.coprime_prod_right_iff.mpr (fun j _ => hcop j)
  rw [← natDivisibilityIndicator_mul q _ n hc]
  ring

noncomputable def tupleCenteredProfile {J : ℕ} (P : Fin J → Finset ℕ)
    (q : ℕ) (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l]
    (b : ZMod l) (h n : ℕ) : ℂ :=
  ∑ x : (j : Fin J) → P j,
    if eligible (∏ j, (x j).val) q then
      natDivisibilityIndicator q n *
        (centeredTuple (∏ j, (x j).val).primeFactors (n : ℤ) : ℂ) *
        (progressionSequence liouville l (b * ((q * ∏ j, (x j).val : ℕ) : ZMod l)) n *
          liouville (n + h * (q * ∏ j, (x j).val)))
    else 0

lemma tupleCenteredProfile_expansion {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l] (b : ZMod l) (h n : ℕ) :
    tupleCenteredProfile P q eligible l b h n =
      ∑ I ∈ (univ : Finset (Fin J)).powerset,
        (-1 : ℂ) ^ I.card * tuplePartialProfile P I q eligible l b h n := by
  simp only [tupleCenteredProfile, tuplePartialProfile, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  by_cases he : eligible (∏ j, (x j).val) q
  · simp only [he, ite_true]
    rw [centeredTuple_nat_eq P hprime hdisjoint]
    have hx := tuple_center_padding_expansion (fun j => (x j).val)
      (fun j => hprime j _ (x j).property) (selectedPrimeValues_injective x hdisjoint)
      q n (fun j => hcop j _ (x j).property)
      (progressionSequence liouville l (b * ((q * ∏ j, (x j).val : ℕ) : ZMod l)) n *
        liouville (n + h * (q * ∏ j, (x j).val)))
    apply hx.trans
    apply sum_congr rfl
    intro I _
    ring
  · simp only [he, ite_false, mul_zero, sum_const_zero]

lemma tupleCenteredProfile_nonraw {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l] (b : ZMod l) (h n : ℕ) :
    tupleCenteredProfile P q eligible l b h n - tuplePartialProfile P ∅ q eligible l b h n =
      ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        (-1 : ℂ) ^ I.card * tuplePartialProfile P I q eligible l b h n := by
  rw [tupleCenteredProfile_expansion P hprime hdisjoint q hcop eligible l b h n]
  let F : Finset (Fin J) → ℂ := fun I =>
    (-1 : ℂ) ^ I.card * tuplePartialProfile P I q eligible l b h n
  have he : (univ : Finset (Fin J)).powerset.filter Finset.Nonempty =
      (univ : Finset (Fin J)).powerset.erase ∅ := by
    ext I
    simp only [mem_filter, mem_erase, nonempty_iff_ne_empty]
    exact and_comm
  rw [he]
  change (∑ I ∈ (univ : Finset (Fin J)).powerset, F I) - _ =
    ∑ I ∈ (univ : Finset (Fin J)).powerset.erase ∅, F I
  rw [← sum_erase_add _ F (empty_mem_powerset _)]
  simp only [F, card_empty, pow_zero, one_mul, add_sub_cancel_right]

end TwoPointCorrelations

end OAI
