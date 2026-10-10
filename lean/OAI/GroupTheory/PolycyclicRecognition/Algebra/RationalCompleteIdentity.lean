import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalCoefficientSequence
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomologyColimitKernel
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedIdentityTorsion

namespace OAI

/-! # Rational vanishing gives an integral annihilator of the complete identity

This is the coefficient step in the torsion endgame. Rational vanishing remains
an explicit intermediate premise until the hierarchical argument supplies it.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

instance groupCohomology_integral_additive (n : ℕ) :
    (groupCohomology.functor ℤ G n).Additive where
  map_add {X Y f g} := by
    change HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor ℤ G).map (f + g)) n =
      HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor ℤ G).map f) n +
        HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor ℤ G).map g) n
    rw [CategoryTheory.Functor.map_add, HomologicalComplex.homologyMap_add]

theorem completedCohomologyMap_scalar_identity (m : ℤ) :
    completedCohomologyMap (m • 𝟙 (trivialIntegral G)) (completedIdentity G) =
      m • completedIdentity G := by
  unfold completedIdentity
  rw [completedCohomologyMap_of]
  have hs : normalizedCohomologyStageMap (m • 𝟙 (trivialIntegral G)) 0 =
      m • LinearMap.id := by
    unfold normalizedCohomologyStageMap
    change ((groupCohomology.functor ℤ G 0).map (m • 𝟙 (trivialIntegral G))).hom = _
    rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]
    rfl
  rw [hs]
  change Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward (trivialIntegral G)) 0
    (m • normalizedGroupIdentityClass G 0) = _
  exact map_zsmul _ _ _

theorem TypeFPInfinity.completedIdentity_factorial_annihilator
    (hG : TypeFPInfinity G)
    (hq : completedCohomologyMap (rationalCoefficientInclusion G 0) (completedIdentity G) = 0) :
    ∃ j : ℕ, (j.factorial : ℤ) • completedIdentity G = 0 := by
  obtain ⟨j, hj, he⟩ := hG.completedCohomology_colimit_kernel
    (rationalCoefficientDiagram G) (Rep.trivial ℤ G ℚ) (rationalCoefficientColimit G) 0
    (completedIdentity G) hq
  refine ⟨j, ?_⟩
  change completedCohomologyMap (factorialMultiplier 0 j • 𝟙 (trivialIntegral G))
    (completedIdentity G) = 0 at he
  rw [completedCohomologyMap_scalar_identity, factorialMultiplier_zero] at he
  exact he

theorem TypeFPInfinity.boundedFiniteSubgroupOrders_of_rational_vanishing
    (hG : TypeFPInfinity G)
    (hq : completedCohomologyMap (rationalCoefficientInclusion G 0) (completedIdentity G) = 0) :
    HasBoundedFiniteSubgroupOrders G := by
  obtain ⟨j, hj⟩ := hG.completedIdentity_factorial_annihilator G hq
  exact boundedFiniteSubgroupOrders_of_completedIdentity_torsion (j.factorial : ℤ)
    (by exact_mod_cast Nat.factorial_ne_zero j) hj

theorem TypeFPInfinity.boundedFiniteSubgroupOrders_of_rational_projectiveDimension
    (hG : TypeFPInfinity G) (d : ℕ) [HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) d] :
    HasBoundedFiniteSubgroupOrders G := by
  let := completedCohomology_subsingleton_of_finite_projectiveDimension (Rep.trivial ℤ G ℚ) d
  exact hG.boundedFiniteSubgroupOrders_of_rational_vanishing G (Subsingleton.elim _ _)

end PolycyclicRecognition

end

end OAI
