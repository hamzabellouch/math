import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction

namespace OAI

noncomputable section
namespace PiExponent.ReducedComponentAmple
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}}

def closedBaseChange (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).subscheme ⟶ I.subscheme :=
  (I.comapIso f).hom ≫ pullback.snd f I.subschemeι

instance closedBaseChange_isClosedImmersion (I : X.IdealSheafData)
    (f : Y ⟶ X) [IsClosedImmersion f] : IsClosedImmersion (closedBaseChange I f) := by
  unfold closedBaseChange
  infer_instance

@[reassoc]
theorem closedBaseChange_condition (I : X.IdealSheafData) (f : Y ⟶ X) :
    closedBaseChange I f ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  simp only [closedBaseChange, Category.assoc, ← pullback.condition,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc]

def closedBaseChangeLineIso (I : X.IdealSheafData) (f : Y ⟶ X) (L : LineBundle X) :
    ((L.pullback I.subschemeι).pullback (closedBaseChange I f)).sheaf ≅
      ((L.pullback f).pullback (I.comap f).subschemeι).sheaf :=
  (Scheme.Modules.pullbackComp (closedBaseChange I f) I.subschemeι).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (closedBaseChange_condition I f)).app L.sheaf ≪≫
    ((Scheme.Modules.pullbackComp (I.comap f).subschemeι f).app L.sheaf).symm

theorem isAmple_comap_restriction (I : X.IdealSheafData) (f : Y ⟶ X)
    [IsClosedImmersion f] (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) :
    ((L.pullback f).pullback (I.comap f).subschemeι).IsAmple :=
  PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ (closedBaseChangeLineIso I f L)
    (LineBundle.IsAmple.pullback_closedImmersion _ hL (closedBaseChange I f))

end PiExponent.ReducedComponentAmple

end

end OAI
