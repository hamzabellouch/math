import OAI.NumberTheory.TwoPoint.Walks.WitnessProbabilityWeight

namespace OAI

/-! Padding tests and the retained witness tests pay the missing reciprocal factors together. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def RetainedMainTests {ι : Type*} [DecidableEq ι] (p : ι → ℕ) (S : Finset ι)
    (h B : ℕ) (main : List SignedStep) (x : ι → Fin B) : Prop :=
  ∀ i, i ∉ S → ∀ k : Fin main.length,
    p i ∈ ((main.get k).padding * (main.get k).tuple).primeFactors →
      ((x i).val : ZMod (p i)) = -((wordDisplacement h (main.take k.val) : ℤ) : ZMod (p i))

theorem retainedMainTests_congr {ι : Type*} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (main : List SignedStep)
    (x y : ι → Fin B) (hxy : ∀ i, i ∉ S → x i = y i) :
    RetainedMainTests p S h B main x ↔ RetainedMainTests p S h B main y := by
  constructor
  · intro hx i hi k hk
    rw [← hxy i hi]
    exact hx i hi k hk
  · intro hy i hi k hk
    rw [hxy i hi]
    exact hy i hi k hk

theorem tuple_weight_mul_padding_hybrid_probability_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] (n B h : ℕ) (p : ι → ℕ)
    (hinj : Function.Injective p) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (S : Finset ι) (main : List SignedStep) (word : Fin n → List SignedStep)
    (attachment : Fin n → ℤ)
    (hS : ∀ i ∈ S, p i ∈ wordDivisorPrimeSupport main)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport (recordedWitnessWord main word), ∃ i, p i = q) :
    (∏ i ∈ S, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (fun x => RetainedMainTests p S h B main x ∧
          ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
            ∀ j, AttachedResiduePositiveWord p h (word j) (attachment j) B y) ≤
      ∏ q ∈ wordDivisorPrimeSupport (recordedWitnessWord main word), (q : ℝ)⁻¹ := by
  let words : Fin (n + 1) → List SignedStep := Fin.cases main word
  let atts : Fin (n + 1) → ℤ := Fin.cases 0 attachment
  have hmono :
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (fun x => RetainedMainTests p S h B main x ∧
          ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
            ∀ j, AttachedResiduePositiveWord p h (word j) (attachment j) B y) ≤
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (RetainedWitnessTests p S h B words atts) := by
    apply FiniteLaw.probability_mono_of_imp
    rintro x ⟨hm, y, hy, hw⟩ i hi j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [words, atts, Fin.cases_zero, zero_add] using hm i hi
    · intro k hk
      rw [← hy i hi]
      exact hw j k i hk
  have hb := hmono.trans (retained_witness_probability_le (n + 1) B h p hp hpB S words atts)
  apply (mul_le_mul_of_nonneg_left hb (prod_nonneg (fun _ _ => by positivity))).trans_eq
  rw [main_witness_reciprocal_product]
  have hw (q : ℕ) : (∃ j, q ∈ wordDivisorPrimeSupport (words j)) ↔
      q ∈ wordDivisorPrimeSupport (recordedWitnessWord main word) := by
    rw [recordedWitnessWord_support, mem_union, mem_biUnion]
    constructor
    · rintro ⟨j, hj⟩
      refine Fin.cases ?_ (fun i => ?_) j hj
      · exact fun hj => Or.inl hj
      · exact fun hj => Or.inr ⟨i, mem_univ _, hj⟩
    · rintro (hm | ⟨j, _, hj⟩)
      · exact ⟨0, hm⟩
      · exact ⟨j.succ, hj⟩
  have he : S ∪ univ.filter (fun i => ∃ j, p i ∈ wordDivisorPrimeSupport (words j)) =
      univ.filter (fun i => p i ∈ wordDivisorPrimeSupport (recordedWitnessWord main word)) := by
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and, hw]
    constructor
    · rintro (hi | hi)
      · rw [recordedWitnessWord_support]
        exact mem_union_left _ (hS i hi)
      · exact hi
    · intro hi
      exact Or.inr hi
  rw [he]
  exact coordinate_reciprocal_product p hinj _ hcover

end TwoPointCorrelations

end OAI
