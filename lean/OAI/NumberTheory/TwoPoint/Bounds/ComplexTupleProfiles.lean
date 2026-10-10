import OAI.NumberTheory.TwoPoint.Bounds.CenteredTupleProfiles

namespace OAI

/-! Exact centered tuple expansion for arbitrary complex sequences. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def tupleComplexPartialProfile {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (q : ℕ) (eligible : ℕ → ℕ → Prop)
    (F G : ℕ → ℂ) (h n : ℕ) : ℂ :=
  ∑ x : (j : Fin J) → P j,
    if eligible (∏ j, (x j).val) q then
      ((∏ i : I, (x i).val : ℕ) : ℂ)⁻¹ *
        (natDivisibilityIndicator (q * ∏ j : {j // j ∉ I}, (x j).val) n *
          (F n * G (n + h * (q * ∏ j, (x j).val))))
    else 0

noncomputable def tupleComplexCenteredProfile {J : ℕ} (P : Fin J → Finset ℕ)
    (q : ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h n : ℕ) : ℂ :=
  ∑ x : (j : Fin J) → P j,
    if eligible (∏ j, (x j).val) q then
      natDivisibilityIndicator q n *
        (centeredTuple (∏ j, (x j).val).primeFactors (n : ℤ) : ℂ) *
        (F n * G (n + h * (q * ∏ j, (x j).val)))
    else 0

lemma tupleComplexCenteredProfile_expansion {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h n : ℕ) :
    tupleComplexCenteredProfile P q eligible F G h n =
      ∑ I ∈ (univ : Finset (Fin J)).powerset,
        (-1 : ℂ) ^ I.card * tupleComplexPartialProfile P I q eligible F G h n := by
  simp only [tupleComplexCenteredProfile, tupleComplexPartialProfile, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  by_cases he : eligible (∏ j, (x j).val) q
  · simp only [he, ite_true]
    rw [centeredTuple_nat_eq P hprime hdisjoint]
    have hx := tuple_center_padding_expansion (fun j => (x j).val)
      (fun j => hprime j _ (x j).property) (selectedPrimeValues_injective x hdisjoint)
      q n (fun j => hcop j _ (x j).property)
      (F n * G (n + h * (q * ∏ j, (x j).val)))
    apply hx.trans
    apply sum_congr rfl
    intro I _
    ring
  · simp only [he, ite_false, mul_zero, sum_const_zero]

lemma tupleComplexCenteredProfile_nonraw {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h n : ℕ) :
    tupleComplexCenteredProfile P q eligible F G h n - tupleComplexPartialProfile P ∅ q eligible F G h n =
      ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        (-1 : ℂ) ^ I.card * tupleComplexPartialProfile P I q eligible F G h n := by
  rw [tupleComplexCenteredProfile_expansion P hprime hdisjoint q hcop eligible F G h n]
  let H : Finset (Fin J) → ℂ := fun I =>
    (-1 : ℂ) ^ I.card * tupleComplexPartialProfile P I q eligible F G h n
  have he : (univ : Finset (Fin J)).powerset.filter Finset.Nonempty =
      (univ : Finset (Fin J)).powerset.erase ∅ := by
    ext I
    simp only [mem_filter, mem_erase, nonempty_iff_ne_empty]
    exact and_comm
  rw [he]
  change (∑ I ∈ (univ : Finset (Fin J)).powerset, H I) - _ =
    ∑ I ∈ (univ : Finset (Fin J)).powerset.erase ∅, H I
  rw [← sum_erase_add _ H (empty_mem_powerset _)]
  simp only [H, card_empty, pow_zero, one_mul, add_sub_cancel_right]

end TwoPointCorrelations

end OAI
