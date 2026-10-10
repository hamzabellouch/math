import OAI.NumberTheory.TwoPoint.Bounds.PositiveWordProbability

namespace OAI

/-! Padding divisibility in one common residue sample, with arbitrary departures. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingPrimeSupport {R : ℕ} (q : Fin R → ℕ) : Finset ℕ :=
  univ.biUnion (fun i => (q i).primeFactors)

def PaddingResidueEvent {R B : ℕ} (Q : Finset ℕ) (q : Fin R → ℕ)
    (offset : Fin R → ℤ) (y : Q → Fin B) : Prop :=
  ∀ (i : Fin R) (p : Q), p.val ∈ (q i).primeFactors →
    ((y p).val : ZMod p.val) = -((offset i : ℤ) : ZMod p.val)

/-- Repeated padding primes impose compatibility conditions on a single
coordinate. The probability pays only one reciprocal per distinct prime. -/
theorem paddingResidueEvent_probability_le {R : ℕ} (Q : Finset ℕ)
    (q : Fin R → ℕ) (offset : Fin R → ℤ) (B : ℕ)
    (hp : ∀ p ∈ Q, 0 < p) (hpB : ∀ p ∈ Q, p ≤ B)
    (hQ : paddingPrimeSupport q ⊆ Q) :
    (FiniteLaw.independent (fun p : Q =>
      uniformResidueLaw B p.val (hp _ p.property) (hpB _ p.property))).probability
        (PaddingResidueEvent Q q offset) ≤
      ∏ p ∈ paddingPrimeSupport q, (p : ℝ)⁻¹ := by
  classical
  let E (p : Q) (y : Fin B) : Prop := ∀ i : Fin R, p.val ∈ (q i).primeFactors →
    (y.val : ZMod p.val) = -((offset i : ℤ) : ZMod p.val)
  have he : PaddingResidueEvent (B := B) Q q offset = (fun y => ∀ p, E p (y p)) := by
    funext y
    exact propext forall_comm
  rw [he, FiniteLaw.independent_probability_all]
  have hprod : (∏ p : Q, if p.val ∈ paddingPrimeSupport q then (p.val : ℝ)⁻¹ else 1) =
      ∏ p ∈ paddingPrimeSupport q, (p : ℝ)⁻¹ := by
    rw [← prod_filter]
    apply prod_bij (fun p _ => p.val)
    · intro p hp'
      exact (mem_filter.mp hp').2
    · intro p _ r _ hpr
      exact Subtype.ext hpr
    · intro p hp'
      exact ⟨⟨p, hQ hp'⟩, mem_filter.mpr ⟨mem_univ _, hp'⟩, rfl⟩
    · intro p _
      rfl
  rw [← hprod]
  apply prod_le_prod₀
  · intro p _
    exact FiniteLaw.probability_nonneg _ _
  · intro p _
    by_cases hp' : p.val ∈ paddingPrimeSupport q
    · rw [ite_eq_left hp']
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp'
      exact ((uniformResidueLaw B p.val (hp _ p.property) (hpB _ p.property)).probability_mono_of_imp
        (fun y hy => hy i hi)).trans_eq
          (uniformResidueLaw_mod_eq B p.val (hp _ p.property) (hpB _ p.property)
            (-((offset i : ℤ) : ZMod p.val)))
    · rw [ite_eq_right hp']
      exact FiniteLaw.probability_le_one _ _

end TwoPointCorrelations

end OAI
