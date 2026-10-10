import OAI.NumberTheory.TwoPoint.Walks.RetainedWitnessProbability

namespace OAI

/-! Main-word reciprocal factors and the retained new witness factors combine exactly. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma reciprocal_union_split {ι : Type*} [DecidableEq ι] (M W : Finset ι) (weight : ι → ℝ) :
    (∏ i ∈ M, weight i) * (∏ i ∈ W \ M, weight i) = ∏ i ∈ M ∪ W, weight i := by
  have hd : Disjoint M (W \ M) := by
    apply disjoint_left.mpr
    intro i hi hwi
    exact (mem_sdiff.mp hwi).2 hi
  rw [← prod_union hd]
  congr 1
  ext i
  simp only [mem_union, mem_sdiff]
  tauto

lemma freshWitnessCoordinates_eq_diff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (p : ι → ℕ) (S : Finset ι) (word : Fin n → List SignedStep) :
    freshWitnessCoordinates p S word =
      (univ.filter (fun i => ∃ j, p i ∈ wordDivisorPrimeSupport (word j))) \ S := by
  ext i
  simp only [freshWitnessCoordinates, mem_filter, mem_univ, true_and, mem_sdiff]
  tauto

theorem main_witness_reciprocal_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (p : ι → ℕ) (S : Finset ι) (word : Fin n → List SignedStep) :
    (∏ i ∈ S, (p i : ℝ)⁻¹) *
        (∏ i ∈ freshWitnessCoordinates p S word, (p i : ℝ)⁻¹) =
      ∏ i ∈ S ∪ univ.filter (fun i => ∃ j, p i ∈ wordDivisorPrimeSupport (word j)),
        (p i : ℝ)⁻¹ := by
  rw [freshWitnessCoordinates_eq_diff]
  exact reciprocal_union_split _ _ _

end TwoPointCorrelations

end OAI
