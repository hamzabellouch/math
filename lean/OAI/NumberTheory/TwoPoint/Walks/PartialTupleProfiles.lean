import OAI.NumberTheory.TwoPoint.Walks.TupleCenterExpansion
import OAI.NumberTheory.TwoPoint.Bounds.NonrawPrefix

namespace OAI

/-! Reindex the actual partial-centering tuple sum by its retained and
removed supply products. Each removed numerical product occurs once. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def tuplePartialProfile {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (q : ℕ) (eligible : ℕ → ℕ → Prop)
    (l : ℕ) [NeZero l] (b : ZMod l) (h n : ℕ) : ℂ :=
  ∑ x : (j : Fin J) → P j,
    if eligible (∏ j, (x j).val) q then
      ((∏ i : I, (x i).val : ℕ) : ℂ)⁻¹ *
        (natDivisibilityIndicator (q * ∏ j : {j // j ∉ I}, (x j).val) n *
          (progressionSequence liouville l (b * ((q * ∏ j, (x j).val : ℕ) : ZMod l)) n *
            liouville (n + h * (q * ∏ j, (x j).val))))
    else 0

lemma tuplePartialProfile_reindex {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (I : Finset (Fin J)) (q : ℕ) (eligible : ℕ → ℕ → Prop)
    (l : ℕ) [NeZero l] (b : ZMod l) (h n : ℕ) :
    tuplePartialProfile P I q eligible l b h n =
      ∑ y : (j : {j // j ∉ I}) → P j,
        partialLiouvilleProfile l b (q * ∏ j, (y j).val)
          ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h n := by
  let F : ℕ → ℕ → ℂ := fun t z =>
    if eligible (t * z) q then (z : ℂ)⁻¹ *
      (natDivisibilityIndicator (q * t) n *
        (progressionSequence liouville l (b * ((q * t * z : ℕ) : ZMod l)) n *
          liouville (n + h * (q * t * z)))) else 0
  have hs := primeTupleSlice_split_sum P I hprime hdisjoint F
  have hleft : tuplePartialProfile P I q eligible l b h n =
      ∑ x : (j : Fin J) → P j,
        F (∏ j : {j // j ∉ I}, (x j).val) (∏ i : I, (x i).val) := by
    apply sum_congr rfl
    intro x _
    have he : (∏ j : {j // j ∉ I}, (x j).val) * (∏ i : I, (x i).val) =
        ∏ j, (x j).val := by
      have hI := prod_coe_sort I (fun j : Fin J => (x j).val)
      have hIc := (prod_subtype (p := fun j : Fin J => j ∉ I) (F := inferInstance) (univ \ I) (by simp) (fun j : Fin J => (x j).val)).symm
      rw [hI, hIc, ← prod_union sdiff_disjoint, sdiff_union_of_subset (subset_univ I)]
    dsimp only [F]
    simp only [mul_assoc, he]
  rw [hleft, hs]
  apply sum_congr rfl
  intro y _
  rw [partialLiouvilleProfile, mul_sum, sum_filter]
  apply sum_congr rfl
  intro z _
  dsimp only [F]
  split_ifs
  · simp only [mul_assoc]
    ring
  · simp

lemma tuplePartialProfile_prefix {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (I : Finset (Fin J)) (q : ℕ) (hq : 0 < q) (eligible : ℕ → ℕ → Prop)
    (l : ℕ) [NeZero l] (b : ZMod l) (h X : ℕ)
    (hunit : ∀ y : (j : {j // j ∉ I}) → P j,
      IsUnit ((q * ∏ j, (y j).val : ℕ) : ZMod l)) :
    positivePrefix (tuplePartialProfile P I q eligible l b h) X =
      ∑ y : (j : {j // j ∉ I}) → P j,
        positivePrefix (residueScaledRoughProfile l b
          ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h)
          (X / (q * ∏ j, (y j).val)) := by
  simp only [positivePrefix, tuplePartialProfile_reindex P hprime hdisjoint]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  exact partialLiouvilleProfile_prefix l b _ _ h X
    (Nat.mul_pos hq (prod_pos fun j _ => (hprime j _ (y j).property).pos)) (hunit y)

lemma tuplePartialProfile_empty {J : ℕ} (P : Fin J → Finset ℕ)
    (q : ℕ) (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l]
    (b : ZMod l) (h n : ℕ) :
    tuplePartialProfile P ∅ q eligible l b h n =
      ∑ x : (j : Fin J) → P j,
        if eligible (∏ j, (x j).val) q then
          natDivisibilityIndicator (q * ∏ j, (x j).val) n *
            (progressionSequence liouville l (b * ((q * ∏ j, (x j).val : ℕ) : ZMod l)) n *
              liouville (n + h * (q * ∏ j, (x j).val)))
        else 0 := by
  unfold tuplePartialProfile
  apply sum_congr rfl
  intro x _
  have he : (∏ j : {j // j ∉ (∅ : Finset (Fin J))}, (x j).val) =
      ∏ j, (x j).val := (prod_subtype univ (by simp) (fun j => (x j).val)).symm
  simp only [Fintype.prod_empty, Nat.cast_one, inv_one, one_mul, he]

end TwoPointCorrelations

end OAI
