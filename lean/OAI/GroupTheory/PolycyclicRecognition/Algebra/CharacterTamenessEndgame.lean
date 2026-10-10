import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacterScaling
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeCharacterSeparation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacterHemisphereEndgame

namespace OAI

/-! # Finite character tameness supplies a contracting group element

The finite zero-sum obstruction is converted to an actual integral separating
element, and then to the already proved nilpotent finiteness endgame.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra InnerProductSpace IsMulCommutative
variable {Q M E : Type} [CommGroup Q] [AddCommGroup M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_character_hemisphere_of_no_zero_sum
    (ρ : Representation ℤ Q M) [Module.Finite ℤ[Q] ρ.asModule]
    (e : Q →* Multiplicative E)
    (hspan : Submodule.span ℝ (Set.range (fun q => (e q).toAdd)) = ⊤)
    (hcover : ∃ R : ℝ, ∀ x : E, ∃ q, ‖(e q).toAdd - x‖ ≤ R)
    (htame : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (z : ι → E),
      (∀ i, ¬Module.Finite ℤ[characterNonnegativeMonoid (inwardVectorCharacter e (z i))]
        (characterMonoidRepresentation ρ (inwardVectorCharacter e (z i))).asModule) →
      (∑ i, z i) ≠ 0) :
    ∃ t : Q, ∀ v : E, ‖v‖ = 1 → 0 ≤ ⟪v, (e t).toAdd⟫_ℝ →
      Module.Finite ℤ[characterNonnegativeMonoid (inwardVectorCharacter e v)]
        (characterMonoidRepresentation ρ (inwardVectorCharacter e v)).asModule := by
  have hC := badUnitCharacters_compact ρ e hspan
  have hzero := badUnitCharacters_no_convex_zero_of_no_zero_sum ρ e htame
  obtain ⟨t, ht⟩ := exists_lattice_character_separator e hcover hC
    (fun v hv => hv.1) hzero
  refine ⟨t, ?_⟩
  intro v hv hinner
  by_contra hbad
  have hp := ht v ⟨hv, hbad⟩
  change 0 < -⟪v, (e t).toAdd⟫_ℝ at hp
  linarith

variable {G : Type} [Group G] [Group.FG G]

theorem virtualSolvableFiniteDimension_of_character_tameness
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)]
    (e : (G ⧸ N) →* Multiplicative E)
    (hspan : Submodule.span ℝ (Set.range (fun q => (e q).toAdd)) = ⊤)
    (hbounded : ∀ R : ℝ, Set.Finite {q | ‖(e q).toAdd‖ ≤ R})
    (hcover : ∃ R : ℝ, ∀ x : E, ∃ q, ‖(e q).toAdd - x‖ ≤ R)
    (htame : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (z : ι → E),
      (∀ i, ¬Module.Finite ℤ[characterNonnegativeMonoid (inwardVectorCharacter e (z i))]
        (characterMonoidRepresentation (normalQuotientAbelianizationRepresentation N)
          (inwardVectorCharacter e (z i))).asModule) → (∑ i, z i) ≠ 0) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let ρ := normalQuotientAbelianizationRepresentation N
  let : Module.Finite ℤ[G ⧸ N] ρ.asModule :=
    finite_normalQuotientAbelianizationModule_of_abelian_quotient N
  obtain ⟨q, hq⟩ := exists_character_hemisphere_of_no_zero_sum ρ e hspan hcover htame
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact virtualSolvableFiniteDimension_of_character_hemisphere N e hspan hbounded t hq

end PolycyclicRecognition

end

end OAI
