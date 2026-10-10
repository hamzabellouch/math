import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalExtensionColumnHomology

namespace OAI

/-! # Degree zero in the normal coinvariant resolution

Inflated representations have trivial kernel action. Their normal
coinvariants recover the original representation, including its quotient
action.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalCoinvariantsInflationUnit (B : Rep.{0} ℤ (G ⧸ N)) :
    B ⟶ (Rep.res (QuotientGroup.mk' N) B).quotientToCoinvariants N :=
  Rep.ofHom {
    toLinearMap := Representation.Coinvariants.mk _
    isIntertwining' q := by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      rfl }

def normalCoinvariantsInflationIso (B : Rep.{0} ℤ (G ⧸ N)) :
    (Rep.res (QuotientGroup.mk' N) B).quotientToCoinvariants N ≅ B where
  hom := normalCoinvariantsInflationCounit N B
  inv := normalCoinvariantsInflationUnit N B
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Representation.Coinvariants.induction_on with
    | h x => rfl
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl

instance normalCoinvariants_leftAdjoint :
    (Rep.quotientToCoinvariantsFunctor.{0} ℤ N).IsLeftAdjoint :=
  (normalCoinvariantsInflationAdjunction N).isLeftAdjoint

def normalQuotientResolutionZeroHomologyIso
    (P : ProjectiveResolution (trivialIntegral G)) :
    (normalQuotientResolutionComplex N P).homology 0 ≅ trivialIntegral (G ⧸ N) :=
  (P.isoLeftDerivedObj (Rep.quotientToCoinvariantsFunctor.{0} ℤ N) 0).symm ≪≫
    (Rep.quotientToCoinvariantsFunctor.{0} ℤ N).leftDerivedZeroIsoSelf.app
      (trivialIntegral G) ≪≫
    normalCoinvariantsInflationIso N (trivialIntegral (G ⧸ N))

end PolycyclicRecognition

end

end OAI
