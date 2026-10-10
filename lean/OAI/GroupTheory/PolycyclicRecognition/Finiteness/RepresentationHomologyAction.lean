import OAI.GroupTheory.PolycyclicRecognition.Finiteness.QuotientCoinvariantsFiniteness

namespace OAI

/-! # The underlying chain map of a representation action on homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {k Q : Type} [CommRing k] [Group Q]

def underlyingActionNatTrans (q : Q) :
    forget₂ (Rep.{0} k Q) (ModuleCat k) ⟶ forget₂ (Rep.{0} k Q) (ModuleCat k) where
  app A := ModuleCat.ofHom (A.ρ q)
  naturality {A B} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Rep.hom_comm_apply f q x).symm

def underlyingChainAction (C : ChainComplex (Rep.{0} k Q) ℕ) (q : Q) :
    ((forget₂ (Rep.{0} k Q) (ModuleCat k)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C ⟶
      ((forget₂ (Rep.{0} k Q) (ModuleCat k)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C :=
  (NatTrans.mapHomologicalComplex (underlyingActionNatTrans q)
    (ComplexShape.down ℕ)).app C

theorem underlyingHomologyAction (C : ChainComplex (Rep.{0} k Q) ℕ) (q : Q) (i : ℕ) :
    ModuleCat.ofHom ((C.homology i).ρ q) =
      ((C.sc i).mapHomologyIso (forget₂ (Rep.{0} k Q) (ModuleCat k))).inv ≫
        HomologicalComplex.homologyMap (underlyingChainAction C q) i ≫
          ((C.sc i).mapHomologyIso (forget₂ (Rep.{0} k Q) (ModuleCat k))).hom := by
  exact NatTrans.app_homology (underlyingActionNatTrans q) (C.sc i)

end PolycyclicRecognition

end

end OAI
