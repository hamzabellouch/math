import OAI.GroupTheory.PolycyclicRecognition.Finiteness.QuotientCoinvariantsFiniteness

namespace OAI

/-! # Iterating normal-subgroup and quotient coinvariants

The two successive quotient maps have exactly the same quotient as taking
coinvariants of the original group. This is the degree-zero comparison used
in the central-filtration homology construction.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep ℤ G)

def normalCoinvariantsToCoinvariants :
    Representation.Coinvariants (A.ρ.comp N.subtype) →ₗ[ℤ]
      Representation.Coinvariants A.ρ :=
  Representation.Coinvariants.lift (A.ρ.comp N.subtype)
    (Representation.Coinvariants.mk A.ρ) (fun n => by
      apply LinearMap.ext
      intro x
      exact Representation.Coinvariants.mk_self_apply A.ρ (n : G) x)

def iteratedCoinvariantsToCoinvariants :
    Representation.Coinvariants (A.quotientToCoinvariants N).ρ →ₗ[ℤ]
      Representation.Coinvariants A.ρ :=
  Representation.Coinvariants.lift (A.quotientToCoinvariants N).ρ
    (normalCoinvariantsToCoinvariants N A) (fun q => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      apply LinearMap.ext
      intro x
      induction x using Representation.Coinvariants.induction_on with
      | h x =>
        change Representation.Coinvariants.mk A.ρ (A.ρ g x) =
          Representation.Coinvariants.mk A.ρ x
        exact Representation.Coinvariants.mk_self_apply A.ρ g x)

def coinvariantsToIteratedCoinvariants :
    Representation.Coinvariants A.ρ →ₗ[ℤ]
      Representation.Coinvariants (A.quotientToCoinvariants N).ρ :=
  Representation.Coinvariants.lift A.ρ
    ((Representation.Coinvariants.mk (A.quotientToCoinvariants N).ρ).comp
      (Representation.Coinvariants.mk (A.ρ.comp N.subtype))) (fun g => by
        apply LinearMap.ext
        intro x
        change Representation.Coinvariants.mk (A.quotientToCoinvariants N).ρ
            (Representation.Coinvariants.mk (A.ρ.comp N.subtype) (A.ρ g x)) =
          Representation.Coinvariants.mk (A.quotientToCoinvariants N).ρ
            (Representation.Coinvariants.mk (A.ρ.comp N.subtype) x)
        exact Representation.Coinvariants.mk_self_apply (A.quotientToCoinvariants N).ρ
          (QuotientGroup.mk' N g) (Representation.Coinvariants.mk (A.ρ.comp N.subtype) x))

def iteratedCoinvariantsEquiv :
    Representation.Coinvariants (A.quotientToCoinvariants N).ρ ≃ₗ[ℤ]
      Representation.Coinvariants A.ρ :=
  LinearEquiv.ofLinearMap (iteratedCoinvariantsToCoinvariants N A)
    (coinvariantsToIteratedCoinvariants N A)
    (by
      apply LinearMap.ext
      intro x
      induction x using Representation.Coinvariants.induction_on with
      | h x => rfl)
    (by
      apply LinearMap.ext
      intro x
      induction x using Representation.Coinvariants.induction_on with
      | h x =>
        induction x using Representation.Coinvariants.induction_on with
        | h x => rfl)

@[simp] theorem iteratedCoinvariantsEquiv_mk (x : A.V) :
    iteratedCoinvariantsEquiv N A
      (Representation.Coinvariants.mk (A.quotientToCoinvariants N).ρ
        (Representation.Coinvariants.mk (A.ρ.comp N.subtype) x)) =
      Representation.Coinvariants.mk A.ρ x := rfl

end PolycyclicRecognition

end

end OAI
