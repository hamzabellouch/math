import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap

namespace OAI

noncomputable section
namespace PiExponent.IdealSectionRestriction
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}}

def sectionsEquiv (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) :
    Γ(closedModule I, f ''ᵁ U) ≃+ Γ(closedModule (I.comap f), U) :=
  ((closedModule I).restrictAppIso f U).symm.addCommGroupIsoToAddEquiv.trans
    (asIso ((closedModuleRestrictIso I f).hom.app U)).addCommGroupIsoToAddEquiv

theorem sectionsEquiv_inclusion (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (s : Γ(closedModule I, f ''ᵁ U)) :
    (closedInclusion (I.comap f)).app U (sectionsEquiv I f U s) =
      (f.appIso U).hom ((closedInclusion I).app (f ''ᵁ U) s) := by
  have h := congrArg (fun g => g.app U s) (restrictedToClosed_inclusion I f)
  exact h

theorem inclusion_injective (I : Y.IdealSheafData) (U : Y.Opens) :
    Function.Injective ((closedInclusion I).app U) := by
  let : Mono (closedInclusion I).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules Y).map (closedInclusion I)))
  exact PresheafOfModules.injective_of_mono (closedInclusion I).val (op U)

def pullback (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    Γ(closedModule I,U) →+ Γ(closedModule (I.comap f),V) :=
  ((closedModule (I.comap f)).presheaf.map (homOfLE h).op).hom.comp
    ((GeometrySupport.IdealPullbackMap.comap f I).app U).hom

theorem pullback_inclusion (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (s : Γ(closedModule I,U)) :
    (closedInclusion (I.comap f)).app V (pullback f I U V h s) =
      f.appLE U V h ((closedInclusion I).app U s) := by
  have hn := PresheafOfModules.naturality_apply (closedInclusion (I.comap f)).val
    (homOfLE h).op ((GeometrySupport.IdealPullbackMap.comap f I).app U s)
  change (closedInclusion (I.comap f)).app V (pullback f I U V h s) =
    X.presheaf.map (homOfLE h).op
      ((closedInclusion (I.comap f)).app (f ⁻¹ᵁ U)
        ((GeometrySupport.IdealPullbackMap.comap f I).app U s)) at hn
  have he := congrArg (fun g => g.app U s)
    (GeometrySupport.IdealPullbackMap.comap_inclusion f I)
  exact hn.trans (congrArg (X.presheaf.map (homOfLE h).op) he)

theorem pullback_eq_sectionsEquiv (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] [QuasiCompact f] (U : X.Opens) :
    pullback f I (f ''ᵁ U) U (f.preimage_image_eq U).ge =
      (sectionsEquiv I f U).toAddMonoidHom := by
  ext s
  apply inclusion_injective (I.comap f) U
  have he := sectionsEquiv_inclusion I f U s
  rw [Scheme.Hom.appIso_hom'] at he
  exact (pullback_inclusion f I (f ''ᵁ U) U (f.preimage_image_eq U).ge s).trans he.symm

def idealCongr {I J : Y.IdealSheafData} (h : I = J) (U : Y.Opens) :
    Γ(closedModule I,U) ≃+ Γ(closedModule J,U) := by
  subst J
  exact AddEquiv.refl _

theorem idealCongr_inclusion {I J : Y.IdealSheafData} (h : I = J) (U : Y.Opens)
    (s : Γ(closedModule I,U)) :
    (closedInclusion J).app U (idealCongr h U s) = (closedInclusion I).app U s := by
  subst J
  rfl

theorem pullback_comp {Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g] (I : Z.IdealSheafData)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ f ⁻¹ᵁ V) (s : Γ(closedModule I,U)) :
    pullback f (I.comap g) V W hW (pullback g I U V hV s) =
      idealCongr (I.comap_comp f g) W
        (pullback (f ≫ g) I U W
          (hW.trans ((Opens.map f.base).map (homOfLE hV)).le) s) := by
  apply inclusion_injective ((I.comap g).comap f) W
  rw [idealCongr_inclusion]
  have h₁ := pullback_inclusion f (I.comap g) V W hW (pullback g I U V hV s)
  have h₂ := pullback_inclusion g I U V hV s
  have h₃ := pullback_inclusion (f ≫ g) I U W
    (hW.trans ((Opens.map f.base).map (homOfLE hV)).le) s
  exact (h₁.trans (congrArg (f.appLE V W hW) h₂)).trans
    ((congrArg (fun k : Γ(Z,U) ⟶ Γ(X,W) => k ((closedInclusion I).app U s))
      (Scheme.Hom.appLE_comp_appLE f g U V W hV hW)).trans h₃.symm)

theorem pullback_self (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (U : Y.Opens) :
    pullback f I U (f ⁻¹ᵁ U) le_rfl =
      ((GeometrySupport.IdealPullbackMap.comap f I).app U).hom := by
  ext s
  exact congrArg (fun a => a ((GeometrySupport.IdealPullbackMap.comap f I).app U s))
    ((closedModule (I.comap f)).presheaf.map_id (op (f ⁻¹ᵁ U)))

theorem pullback_bijective_iff_comap (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (he : V = f ⁻¹ᵁ U) :
    Function.Bijective (pullback f I U V h) ↔
      Function.Bijective ((GeometrySupport.IdealPullbackMap.comap f I).app U) := by
  subst V
  rw [pullback_self]
  rfl

end PiExponent.IdealSectionRestriction

end

end OAI
