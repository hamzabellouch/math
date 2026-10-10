import OAI.NumberTheory.TwoPoint.Walks.WitnessReciprocalUnion
import OAI.NumberTheory.TwoPoint.Bounds.RecordedWitnessSegments

namespace OAI

/-! The retained-witness probability pays exactly the full numerical prime weight. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma wordDivisorPrimeSupport_append (v w : List SignedStep) :
    wordDivisorPrimeSupport (v ++ w) =
      wordDivisorPrimeSupport v ∪ wordDivisorPrimeSupport w := by
  simp only [wordDivisorPrimeSupport, List.toFinset_append, union_biUnion]

lemma recordedWitnessWord_support {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) :
    wordDivisorPrimeSupport (recordedWitnessWord main word) =
      wordDivisorPrimeSupport main ∪ univ.biUnion (fun j => wordDivisorPrimeSupport (word j)) := by
  rw [recordedWitnessWord, wordDivisorPrimeSupport_append]
  congr 1
  ext p
  simp only [wordDivisorPrimeSupport, mem_biUnion, List.mem_toFinset,
    List.mem_flatten, List.mem_ofFn, mem_univ, true_and]
  constructor
  · rintro ⟨a, ⟨_, ⟨i, rfl⟩, ha⟩, hp⟩
    exact ⟨i, a, ha, hp⟩
  · rintro ⟨i, a, ha, hp⟩
    exact ⟨a, ⟨word i, ⟨i, rfl⟩, ha⟩, hp⟩

lemma coordinate_reciprocal_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hinj : Function.Injective p) (Q : Finset ℕ)
    (hcover : ∀ q ∈ Q, ∃ i, p i = q) :
    (∏ i ∈ univ.filter (fun i => p i ∈ Q), (p i : ℝ)⁻¹) =
      ∏ q ∈ Q, (q : ℝ)⁻¹ := by
  have he : (univ.filter (fun i => p i ∈ Q)).image p = Q := by
    ext q
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hq
      obtain ⟨i, rfl⟩ := hcover q hq
      exact ⟨i, hq, rfl⟩
  conv_rhs => rw [← he, prod_image (fun i _ j _ hij => hinj hij)]

theorem main_weight_mul_hybrid_probability_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n B h : ℕ) (p : ι → ℕ) (hinj : Function.Injective p)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (main : List SignedStep) (word : Fin n → List SignedStep) (attachment : Fin n → ℤ)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport (recordedWitnessWord main word),
      ∃ i, p i = q) :
    (∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (fun x => ∃ y : ι → Fin B,
          (∀ i, p i ∉ wordDivisorPrimeSupport main → y i = x i) ∧
          ∀ j, AttachedResiduePositiveWord p h (word j) (attachment j) B y) ≤
      ∏ q ∈ wordDivisorPrimeSupport (recordedWitnessWord main word), (q : ℝ)⁻¹ := by
  let S := univ.filter (fun i => p i ∈ wordDivisorPrimeSupport main)
  have hmcover : ∀ q ∈ wordDivisorPrimeSupport main, ∃ i, p i = q := by
    intro q hq
    apply hcover q
    rw [recordedWitnessWord_support]
    exact mem_union_left _ hq
  have hevent : (fun x : ι → Fin B => ∃ y : ι → Fin B,
      (∀ i, p i ∉ wordDivisorPrimeSupport main → y i = x i) ∧
      ∀ j, AttachedResiduePositiveWord p h (word j) (attachment j) B y) =
      (fun x : ι → Fin B => ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
      ∀ j, AttachedResiduePositiveWord p h (word j) (attachment j) B y) := by
    simp only [S, mem_filter, mem_univ, true_and]
  rw [hevent, ← coordinate_reciprocal_product p hinj _ hmcover]
  apply (mul_le_mul_of_nonneg_left
    (hybrid_witness_probability_le n B h p hp hpB S word attachment)
    (prod_nonneg (fun _ _ => by positivity))).trans_eq
  rw [main_witness_reciprocal_product]
  have he : S ∪ univ.filter (fun i => ∃ j, p i ∈ wordDivisorPrimeSupport (word j)) =
      univ.filter (fun i => p i ∈ wordDivisorPrimeSupport (recordedWitnessWord main word)) := by
    ext i
    simp only [S, recordedWitnessWord_support, mem_union, mem_filter, mem_univ,
      true_and, mem_biUnion]
  rw [he]
  exact coordinate_reciprocal_product p hinj _ hcover

end TwoPointCorrelations

end OAI
