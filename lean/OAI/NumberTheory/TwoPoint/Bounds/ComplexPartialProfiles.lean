import OAI.NumberTheory.TwoPoint.Bounds.ComplexTupleProfiles

namespace OAI

/-! Exact retained/removed tuple reindexing and divisibility extraction for complex tests. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def complexRoughProfile (F G : ℕ → ℂ) (Z : Finset ℕ) (h n : ℕ) : ℂ :=
  ∑ z ∈ Z, (z : ℂ)⁻¹ * (F n * G (n + h * z))

noncomputable def complexPartialProfile (F G : ℕ → ℂ) (u : ℕ) (Z : Finset ℕ)
    (h n : ℕ) : ℂ :=
  natDivisibilityIndicator u n * ∑ z ∈ Z, (z : ℂ)⁻¹ * (F n * G (n + h * u * z))

lemma complexPartialProfile_prefix (F G : ℕ → ℂ) (u : ℕ) (Z : Finset ℕ)
    (h X : ℕ) (hu : 0 < u) :
    positivePrefix (complexPartialProfile F G u Z h) X =
      positivePrefix (complexRoughProfile (fun n => F (u * n)) (fun n => G (u * n)) Z h)
        (X / u) := by
  unfold complexPartialProfile
  rw [divisibility_positivePrefix _ u X hu]
  congr 1
  funext n
  unfold complexRoughProfile
  apply sum_congr rfl
  intro z _
  rw [show u * n + h * u * z = u * (n + h * z) by ring]

lemma tupleComplexPartialProfile_reindex {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (I : Finset (Fin J)) (q : ℕ) (eligible : ℕ → ℕ → Prop)
    (F G : ℕ → ℂ) (h n : ℕ) :
    tupleComplexPartialProfile P I q eligible F G h n =
      ∑ y : (j : {j // j ∉ I}) → P j,
        complexPartialProfile F G (q * ∏ j, (y j).val)
          ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h n := by
  let H : ℕ → ℕ → ℂ := fun t z =>
    if eligible (t * z) q then (z : ℂ)⁻¹ *
      (natDivisibilityIndicator (q * t) n *
        (F n * G (n + h * (q * t * z)))) else 0
  have hs := primeTupleSlice_split_sum P I hprime hdisjoint H
  have hleft : tupleComplexPartialProfile P I q eligible F G h n =
      ∑ x : (j : Fin J) → P j,
        H (∏ j : {j // j ∉ I}, (x j).val) (∏ i : I, (x i).val) := by
    apply sum_congr rfl
    intro x _
    have he : (∏ j : {j // j ∉ I}, (x j).val) * (∏ i : I, (x i).val) =
        ∏ j, (x j).val := by
      have hI := prod_coe_sort I (fun j : Fin J => (x j).val)
      have hIc := (prod_subtype (p := fun j : Fin J => j ∉ I) (F := inferInstance) (univ \ I) (by simp) (fun j : Fin J => (x j).val)).symm
      rw [hI, hIc, ← prod_union sdiff_disjoint, sdiff_union_of_subset (subset_univ I)]
    dsimp only [H]
    simp only [mul_assoc, he]
  rw [hleft, hs]
  apply sum_congr rfl
  intro y _
  rw [complexPartialProfile, mul_sum, sum_filter]
  apply sum_congr rfl
  intro z _
  dsimp only [H]
  split_ifs
  · simp only [mul_assoc]
    ring
  · simp

lemma tupleComplexPartialProfile_prefix {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (I : Finset (Fin J)) (q : ℕ) (hq : 0 < q) (eligible : ℕ → ℕ → Prop)
    (F G : ℕ → ℂ) (h X : ℕ)
    :
    positivePrefix (tupleComplexPartialProfile P I q eligible F G h) X =
      ∑ y : (j : {j // j ∉ I}) → P j,
        positivePrefix (complexRoughProfile (fun m => F ((q * ∏ j, (y j).val) * m))
          (fun m => G ((q * ∏ j, (y j).val) * m))
          ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h)
          (X / (q * ∏ j, (y j).val)) := by
  simp only [positivePrefix, tupleComplexPartialProfile_reindex P hprime hdisjoint]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  exact complexPartialProfile_prefix F G _ _ h X
    (Nat.mul_pos hq (prod_pos fun j _ => (hprime j _ (y j).property).pos))

end TwoPointCorrelations

end OAI
