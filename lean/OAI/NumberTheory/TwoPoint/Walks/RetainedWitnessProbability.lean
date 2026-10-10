import OAI.NumberTheory.TwoPoint.Bounds.ResidueWordDependence

namespace OAI

/-! A common hybrid pays one reciprocal for each new witness prime, without counting hybrids. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def freshWitnessCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (p : ι → ℕ) (S : Finset ι) (word : Fin n → List SignedStep) : Finset ι :=
  univ.filter (fun i => i ∉ S ∧ ∃ j, p i ∈ wordDivisorPrimeSupport (word j))

def RetainedWitnessTests {ι : Type*} {n : ℕ} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (word : Fin n → List SignedStep)
    (attachment : Fin n → ℤ) (x : ι → Fin B) : Prop :=
  ∀ i, i ∉ S → ∀ (j : Fin n) (k : Fin (word j).length),
    p i ∈ (((word j).get k).padding * ((word j).get k).tuple).primeFactors →
      ((x i).val : ZMod (p i)) =
        -((attachment j + wordDisplacement h ((word j).take k.val) : ℤ) : ZMod (p i))

theorem retained_witness_probability_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n B h : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (S : Finset ι) (word : Fin n → List SignedStep) (attachment : Fin n → ℤ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
      (RetainedWitnessTests p S h B word attachment) ≤
      ∏ i ∈ freshWitnessCoordinates p S word, (p i : ℝ)⁻¹ := by
  let E (i : ι) (v : Fin B) : Prop := i ∉ S →
    ∀ (j : Fin n) (k : Fin (word j).length),
      p i ∈ (((word j).get k).padding * ((word j).get k).tuple).primeFactors →
        (v.val : ZMod (p i)) =
          -((attachment j + wordDisplacement h ((word j).take k.val) : ℤ) : ZMod (p i))
  change (FiniteLaw.independent _).probability (fun x => ∀ i, E i (x i)) ≤ _
  rw [FiniteLaw.independent_probability_all]
  unfold freshWitnessCoordinates
  rw [prod_filter]
  apply prod_le_prod₀
  · intro i _
    exact FiniteLaw.probability_nonneg _ _
  · intro i _
    by_cases hi : i ∉ S ∧ ∃ j, p i ∈ wordDivisorPrimeSupport (word j)
    · rw [ite_eq_left hi]
      obtain ⟨j, hj⟩ := hi.2
      obtain ⟨k, hk⟩ := (mem_wordDivisorPrimeSupport (word j) (p i)).mp hj
      exact ((uniformResidueLaw B (p i) (hp i) (hpB i)).probability_mono_of_imp
        (fun v hv => hv hi.1 j k hk)).trans_eq (uniformResidueLaw_mod_eq B (p i) (hp i) (hpB i) _)
    · rw [ite_eq_right hi]
      exact FiniteLaw.probability_le_one _ _

theorem hybrid_witness_probability_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n B h : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (S : Finset ι) (word : Fin n → List SignedStep) (attachment : Fin n → ℤ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
      (fun x => ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
        ∀ j, AttachedResiduePositiveWord p h (word j) (attachment j) B y) ≤
      ∏ i ∈ freshWitnessCoordinates p S word, (p i : ℝ)⁻¹ := by
  apply (FiniteLaw.probability_mono_of_imp _ ?_).trans
    (retained_witness_probability_le n B h p hp hpB S word attachment)
  rintro x ⟨y, heq, htests⟩ i hi j k hk
  rw [← heq i hi]
  exact htests j k i hk

end TwoPointCorrelations

end OAI
