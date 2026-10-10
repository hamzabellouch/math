import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Model

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {X Y : Scheme.{0}}

instance opensMap_final (f : Y ⟶ X) : (Opens.map f.base).Final := by
  let : PreservesLimit (Functor.empty.{0} X.Opens) (Opens.map f.base) := by
    apply preservesLimit_of_preserves_limit_cone (isTerminalTop (α := X.Opens))
    exact (isLimitMapConeEmptyConeEquiv (Opens.map f.base) (⊤ : X.Opens)).symm isTerminalTop
  infer_instance

def pullbackRestrictIso (f : Y ⟶ X) (L : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (L.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
  (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L ≪≫
  (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L ≪≫
  ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app L).symm ≪≫
  (Scheme.Modules.pullback (f ∣_ U)).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm

def LineBundle.pullback (L : LineBundle X) (f : Y ⟶ X) : LineBundle Y where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  locallyRankOne y := by
    obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
    refine ⟨f ⁻¹ᵁ U,hy,⟨pullbackRestrictIso f L.sheaf U ≪≫
      (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫ ?_⟩⟩
    letI : (Opens.map (f ∣_ U).base).Final := opensMap_final (f ∣_ U)
    letI : (SheafOfModules.pushforward (f ∣_ U).toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward (f ∣_ U)).IsRightAdjoint
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
        (F := Opens.map (f ∣_ U).base) (f ∣_ U).toRingCatSheafHom) :=
      SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
        (F := Opens.map (f ∣_ U).base) (f ∣_ U).toRingCatSheafHom
    let unitIso :=
      asIso (C := SheafOfModules (f ⁻¹ᵁ U).toScheme.ringCatSheaf)
        (SheafOfModules.pullbackObjUnitToUnit (F := Opens.map (f ∣_ U).base)
        (f ∣_ U).toRingCatSheafHom)
    exact
      { hom := unitIso.hom
        inv := unitIso.inv
        hom_inv_id := unitIso.hom_inv_id
        inv_hom_id := unitIso.inv_hom_id }

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
