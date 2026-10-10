import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IteratedCoinvariantsHomology
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

namespace OAI

/-! # Normal coinvariants preserve projective representations

The right adjoint is the actual inflation along the quotient homomorphism.
This gives projective terms in the quotient complex used for the higher
central-filtration comparison.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalCoinvariantsInflationCounit (B : Rep.{0} ℤ (G ⧸ N)) :
    (Rep.res (QuotientGroup.mk' N) B).quotientToCoinvariants N ⟶ B :=
  Rep.ofHom {
    toLinearMap := Representation.Coinvariants.lift _ LinearMap.id (fun n => by
      apply LinearMap.ext
      intro x
      change B.ρ (QuotientGroup.mk' N (n : G)) x = x
      have hn : QuotientGroup.mk' N (n : G) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr n.property
      rw [hn, map_one]
      rfl)
    isIntertwining' q := by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
      apply LinearMap.ext
      intro x
      induction x using Representation.Coinvariants.induction_on with
      | h x => rfl }

@[simp] theorem normalCoinvariantsInflationCounit_mk (B : Rep.{0} ℤ (G ⧸ N)) (x : B.V) :
    normalCoinvariantsInflationCounit N B
      (Representation.Coinvariants.mk ((Rep.res (QuotientGroup.mk' N) B).ρ.comp N.subtype) x) = x := rfl

def normalCoinvariantsInflationAdjunction :
    Rep.quotientToCoinvariantsFunctor.{0} ℤ N ⊣ Rep.resFunctor (QuotientGroup.mk' N) where
  unit := {
    app A := A.toCoinvariantsMkQ N
    naturality := by intros; ext; rfl }
  counit := {
    app B := normalCoinvariantsInflationCounit N B
    naturality := by
      intro A B f
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      induction x using Representation.Coinvariants.induction_on with
      | h x => rfl }
  left_triangle_components := by
    intro A
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Representation.Coinvariants.induction_on with
    | h x => rfl
  right_triangle_components := by intros; ext; rfl

instance normalCoinvariants_preservesProjective :
    (Rep.quotientToCoinvariantsFunctor.{0} ℤ N).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (normalCoinvariantsInflationAdjunction N)

instance normalCoinvariantsResolutionTerm_projective
    (P : ProjectiveResolution (trivialIntegral G)) (i : ℕ) :
    Projective ((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).obj (P.complex.X i)) :=
  Functor.projective_obj _ _

end PolycyclicRecognition

end

end OAI
