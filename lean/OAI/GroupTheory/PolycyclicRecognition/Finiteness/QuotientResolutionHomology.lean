import OAI.GroupTheory.PolycyclicRecognition.Finiteness.QuotientCoinvariantsFiniteness
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

namespace OAI

/-! # Normal coinvariants of an ambient projective resolution

Forgetting the quotient action recovers the ordinary integral homology of the
normal subgroup. The comparison retains the chosen ambient resolution.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def quotientCoinvariantsUnderlyingIso :
    Rep.quotientToCoinvariantsFunctor.{0} ℤ N ⋙
        forget₂ (Rep.{0} ℤ (G ⧸ N)) (ModuleCat ℤ) ≅
      Rep.resFunctor.{0} N.subtype ⋙ Rep.coinvariantsFunctor ℤ N :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def trivialCoinvariantsTensorIso :
    Rep.coinvariantsFunctor.{0} ℤ N ≅
      (Rep.coinvariantsTensor ℤ N).obj (Rep.trivial ℤ N ℤ) :=
  NatIso.ofComponents
    (fun A => (Rep.coinvariantsFunctor ℤ N).mapIso (λ_ A).symm) (by
      intro A B f
      change (Rep.coinvariantsFunctor ℤ N).map f ≫
          (Rep.coinvariantsFunctor ℤ N).map (λ_ B).inv =
        (Rep.coinvariantsFunctor ℤ N).map (λ_ A).inv ≫
          (Rep.coinvariantsFunctor ℤ N).map ((𝟙 (𝟙_ (Rep ℤ N))) ⊗ₘ f)
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1)

def quotientResolutionHomologyIso
    (P : ProjectiveResolution (trivialIntegral G)) (i : ℕ) :
    (forget₂ (Rep.{0} ℤ (G ⧸ N)) (ModuleCat ℤ)).obj
        ((((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex).homology i) ≅
      groupHomology (Rep.trivial ℤ N ℤ) i := by
  classical
  let F := Rep.quotientToCoinvariantsFunctor.{0} ℤ N
  let U := forget₂ (Rep.{0} ℤ (G ⧸ N)) (ModuleCat ℤ)
  let C := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let e := quotientCoinvariantsUnderlyingIso N ≪≫
    Functor.isoWhiskerLeft (Rep.resFunctor.{0} N.subtype) (trivialCoinvariantsTensorIso N)
  let ec := (NatIso.mapHomologicalComplex e (ComplexShape.down ℕ)).app P.complex
  exact ((C.sc i).mapHomologyIso U).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapIso ec ≪≫
      (groupHomologyIso (Rep.trivial ℤ N ℤ) i
        ((Rep.resFunctor.{0} N.subtype).mapProjectiveResolution P)).symm

end PolycyclicRecognition

end

end OAI
