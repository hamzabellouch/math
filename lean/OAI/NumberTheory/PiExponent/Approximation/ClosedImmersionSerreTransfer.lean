import OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open PiExponentSeshadri.FlasqueCohomology

namespace PiExponent.ClosedImmersionSerreTransfer

universe u
private abbrev schemeUnit (Z : Scheme.{u}) : Z.Modules :=
  SheafOfModules.unit Z.ringCatSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def structureMap : schemeUnit Y ⟶
    (Scheme.Modules.pushforward f).obj (schemeUnit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

lemma globalHom_push (M : X.Modules) (g : schemeUnit X ⟶ M) :
    globalHomEquiv Y.ringCatSheaf ((Scheme.Modules.pushforward f).obj M)
      (structureMap f ≫ (Scheme.Modules.pushforward f).map g) =
    globalHomEquiv X.ringCatSheaf M g := by
  change (g.val.app (op ⊤)) ((f.app ⊤) 1) = (g.val.app (op ⊤)) (1 : Γ(X,⊤))
  rw [map_one]
  rfl

lemma globalHom_push_bijective (M : X.Modules) :
    Function.Bijective (fun g : schemeUnit X ⟶ M =>
      structureMap f ≫ (Scheme.Modules.pushforward f).map g) := by
  constructor
  · intro a b h
    apply (globalHomEquiv X.ringCatSheaf M).injective
    exact (globalHom_push f M a).symm.trans
      ((congrArg (globalHomEquiv Y.ringCatSheaf _) h).trans (globalHom_push f M b))
  · intro b
    obtain ⟨a, ha⟩ := (globalHomEquiv X.ringCatSheaf M).surjective
      (globalHomEquiv Y.ringCatSheaf ((Scheme.Modules.pushforward f).obj M) b)
    refine ⟨a, ?_⟩
    apply (globalHomEquiv Y.ringCatSheaf _).injective
    exact (globalHom_push f M a).trans ha

instance pushforward_flasque (M : X.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pushforward f).obj M)) :=
  TopCat.Sheaf.IsFlasque.pushforward_isFlasque
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) f.base

local instance : HasExt.{u+1} X.Modules := HasExt.standard _
local instance : HasExt.{u+1} Y.Modules := HasExt.standard _

variable [PreservesFiniteColimits (Scheme.Modules.pushforward f)]

def cohomologyMap (M : X.Modules) (n : ℕ) :
    Ext.{u+1} (C := X.Modules) (schemeUnit X) M n →+
      Ext.{u+1} (C := Y.Modules) (schemeUnit Y)
        ((Scheme.Modules.pushforward f).obj M) n :=
  PiExponentSeshadri.ExtSectionComparison.mapFrom
    (Scheme.Modules.pushforward f) (structureMap f) M n

theorem cohomologyMap_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (cohomologyMap f M n) := by
  let : EnoughInjectives X.Modules :=
    PiExponentSeshadri.ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  apply PiExponentSeshadri.ExtSectionComparison.mapFrom_bijective
  · exact globalHom_push_bijective f
  · intro I hI q x
    let : Injective (C := SheafOfModules X.ringCatSheaf) I := hI
    let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj I) :=
      PiExponentSeshadri.ModuleFlasque.injective_isFlasque X.ringCatSheaf I
    exact flasque_ext_zero Y.ringCatSheaf q ((Scheme.Modules.pushforward f).obj I) x

def cohomologyEquiv (M : X.Modules) (n : ℕ) :
    Ext.{u+1} (C := X.Modules) (schemeUnit X) M n ≃+
      Ext.{u+1} (C := Y.Modules) (schemeUnit Y)
        ((Scheme.Modules.pushforward f).obj M) n :=
  AddEquiv.ofBijective (cohomologyMap f M n) (cohomologyMap_bijective f M n)

theorem ext_zero_iff (M : X.Modules) (n : ℕ) :
    (∀ x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M n, x = 0) ↔
      (∀ x : Ext.{u+1} (C := Y.Modules) (schemeUnit Y)
        ((Scheme.Modules.pushforward f).obj M) n, x = 0) := by
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := (cohomologyEquiv f M n).surjective x
    rw [h y, map_zero]
  · intro h x
    apply (cohomologyEquiv f M n).injective
    rw [map_zero]
    exact h _

def closedCohomologyEquiv {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsClosedImmersion f] (M : X.Modules) (n : ℕ) :
    Ext.{1} (C := X.Modules) (schemeUnit X) M n ≃+
      Ext.{1} (C := Y.Modules) (schemeUnit Y)
        ((Scheme.Modules.pushforward f).obj M) n :=
  cohomologyEquiv f M n

end PiExponent.ClosedImmersionSerreTransfer

end

end OAI
