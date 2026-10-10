import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalAbelianizationQuotient
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CharacterHemisphereContraction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PowersModuleAscendingBase

namespace OAI

/-! # The character hemisphere criterion reaches the nilpotent endgame

Finite module generation over the quotient ring comes from the group itself.
The hemisphere condition supplies an actual ascending base for conjugation.
The still separate FP-infinity implication must supply that condition and the
nilpotent-by-abelian structure; neither is introduced as a new main input.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra InnerProductSpace IsMulCommutative
variable {G E : Type} [Group G] [Group.FG G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

theorem virtualSolvableFiniteDimension_of_character_hemisphere
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)]
    (e : (G ⧸ N) →* Multiplicative E)
    (hspan : Submodule.span ℝ (Set.range (fun q => (e q).toAdd)) = ⊤)
    (hbounded : ∀ R : ℝ, Set.Finite {q | ‖(e q).toAdd‖ ≤ R}) (t : G)
    (hfinite : ∀ v : E, ‖v‖ = 1 → 0 ≤ ⟪v, (e (QuotientGroup.mk' N t)).toAdd⟫_ℝ →
      Module.Finite ℤ[characterNonnegativeMonoid (inwardVectorCharacter e v)]
        (characterMonoidRepresentation (normalQuotientAbelianizationRepresentation N)
          (inwardVectorCharacter e v)).asModule) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let ρ := normalQuotientAbelianizationRepresentation N
  let : Module.Finite ℤ[G ⧸ N] ρ.asModule :=
    finite_normalQuotientAbelianizationModule_of_abelian_quotient N
  have hcyclic := finite_cyclicMonoidModule_of_character_hemisphere ρ e hspan hbounded
    (QuotientGroup.mk' N t) hfinite
  let := hcyclic
  apply virtualSolvableFiniteDimension_of_abelianByFinite_contractor N ⊤ t
  apply ascendingBase_of_powersMonoidModule ρ (QuotientGroup.mk' N t)
  intro x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (commutator N) x
  rfl

end PolycyclicRecognition

end

end OAI
