import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
variable {X Y : Scheme.{0}}

def unitMap (f : Y ⟶ X) : structureSheaf X ⟶
    (Scheme.Modules.pushforward f).obj (structureSheaf Y) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

theorem unitMap_mono (f : Y ⟶ X) [IsReduced X] [QuasiCompact f] [IsDominant f] :
    Mono (unitMap f) := by
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have h : Mono (unitMap f).val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact f.app_injective U.unop
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map h

theorem dominant_of_iso_restrict [IsIntegral X] (f : Y ⟶ X)
    (U : X.Opens) (hU : U ≠ ⊥) [IsIso (f ∣_ U)] : IsDominant f := by
  have hne : (U : Set X).Nonempty := by
    by_contra hn
    apply hU
    apply SetLike.coe_injective
    exact Set.not_nonempty_iff_eq_empty.mp hn
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense hne)
  have : IsDominant ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact IsDominant.of_comp (f ⁻¹ᵁ U).ι f

theorem unitMap_restrict_isIso (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (unitMap f)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  have h := morphismRestrict_app f U V
  have hiso : IsIso ((f ∣_ U).app V) := by infer_instance
  have : IsIso (f.app (U.ι ''ᵁ V) ≫
      Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op) := by
    rw [← h]
    exact hiso
  have : IsIso (f.app (U.ι ''ᵁ V)) :=
    (isIso_comp_right_iff (f.app (U.ι ''ᵁ V))
      (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)).mp inferInstance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso (f.app (U.ι ''ᵁ V))

theorem unitMap_isoOpen_ne_bot (f : Y ⟶ X) (U : X.Opens)
    (hU : U ≠ ⊥) [IsIso (f ∣_ U)] : isoOpen (unitMap f) ≠ ⊥ := by
  have hle : U ≤ isoOpen (unitMap f) := by
    intro x hx
    exact (mem_isoOpen_iff _ x).mpr ⟨U,hx,unitMap_restrict_isIso f U⟩
  intro h
  exact hU (le_antisymm (h ▸ hle) bot_le)

def pushforwardPullbackIso (f : Y ⟶ X) (L : LineBundle X) :
    moduleTensor X ((Scheme.Modules.pushforward f).obj (structureSheaf Y)) L.sheaf ≅
      (Scheme.Modules.pushforward f).obj (L.pullback f).sheaf :=
  ProjectionFormula.iso f (structureSheaf Y) L ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTensorUnit (L.pullback f).sheaf)

end PiExponent.CurveNormalizationDegree

end

end OAI
