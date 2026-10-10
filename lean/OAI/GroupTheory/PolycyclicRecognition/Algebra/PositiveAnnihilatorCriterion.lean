import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationOrbitGenerators

namespace OAI

/-! # A positive group-ring identity is a finite monoid-module certificate -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {Q M : Type} [CommGroup Q] [AddCommGroup M]

omit [CommGroup Q] in
theorem finite_character_positive_lower_bound (s : Finset Q) (f : Q → ℝ)
    (hf : ∀ q ∈ s, 0 < f q) : ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ s, δ ≤ f q := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert q s hq ih =>
    obtain ⟨δ, hδ, hs⟩ := ih (fun r hr => hf r (Finset.mem_insert_of_mem hr))
    refine ⟨min (f q) δ, lt_min (hf q (Finset.mem_insert_self _ _)) hδ, ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hs r hr)

theorem representation_groupRing_apply (ρ : Representation ℤ Q M) (a : ℤ[Q]) (x : M) :
    ρ.asAlgebraHom a x = ∑ g ∈ a.coeff.support, a.coeff g • ρ g x := by
  simp only [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply,
    Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]

/-- This is the positive identity criterion, with support in the strict
character half-space. It supplies a concrete sufficient Bieri--Strebel direction. -/
theorem finite_characterMonoidModule_of_positive_identity
    (ρ : Representation ℤ Q M) [Module.Finite ℤ[Q] ρ.asModule]
    (χ : Q →* Multiplicative ℝ) (a : ℤ[Q])
    (ha : ∀ g ∈ a.coeff.support, 0 < (χ g).toAdd)
    (hid : ρ.asAlgebraHom a = 1) :
    Module.Finite ℤ[characterNonnegativeMonoid χ] (characterMonoidRepresentation ρ χ).asModule := by
  obtain ⟨δ, hδ, hpos⟩ := finite_character_positive_lower_bound a.coeff.support
    (fun q => (χ q).toAdd) ha
  apply finite_characterMonoidModule_of_positive_relation ρ χ a.coeff.support a.coeff hδ hpos
  intro x
  rw [← representation_groupRing_apply, hid]
  rfl

end PolycyclicRecognition

end

end OAI
