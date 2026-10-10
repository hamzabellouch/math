import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.OpenBaseChange

namespace OAI


                                          
section

namespace MaximalSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def leftSquare :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).symm (rightSquare f U)

lemma unit_compatibility (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (iso f U ((Scheme.Modules.pullback f).obj M)).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M) := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction f
  let b := Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι
  let c := Scheme.Modules.restrictAdjunction U.ι
  let d := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  have h := unit_conjugateEquiv_symm (a.comp b) (c.comp d) (rightSquare f U).hom M
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  change (a.unit.app M ≫ (Scheme.Modules.pushforward f).map
    (b.unit.app ((Scheme.Modules.pullback f).obj M))) ≫
      (rightSquare f U).hom.app _ =
    (c.unit.app M ≫ (Scheme.Modules.pushforward U.ι).map
      (d.unit.app (M.restrict U.ι))) ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M)) at h
  have hc := congrArg (fun q => (Scheme.Modules.restrictFunctor U.ι).map q ≫
    c.counit.app ((Scheme.Modules.pushforward (f ∣_ U)).obj
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι))) h
  simp only [Functor.map_comp, Category.assoc] at hc
  change _ = _ at hc
  have hn := c.counit.naturality
    (d.unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, Functor.map_comp] at hn
  rw [Category.assoc] at hn
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [hn] at hc
  simp only [← Category.assoc] at hc
  have ht := c.left_triangle_components M
  change (Scheme.Modules.restrictFunctor U.ι).map (c.unit.app M) ≫
    c.counit.app (M.restrict U.ι) = 𝟙 _ at ht
  rw [ht, Category.id_comp] at hc
  simpa only [a, b, c, d, iso, asIso_hom, hom, Category.assoc] using hc

end
end MaximalSeshadri.OpenBaseChange

end


end OAI
