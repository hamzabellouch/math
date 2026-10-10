import OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange
import OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor

namespace OAI

noncomputable section

namespace PiExponentSeshadri.OpenBaseChange

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma modules_comp_app {Z : Scheme.{0}} {M N P : Z.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (W : Z.Opens) : (a ≫ b).app W = a.app W ≫ b.app W := rfl

lemma hom_app (M : X.Modules) (V : U.toScheme.Opens) :
    (hom f U M).app V = M.presheaf.map
      (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  change ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app
    (f ⁻¹ᵁ (U.ι ''ᵁ V)) ≫
      ((rightSquare f U).hom.app (M.restrict (f ⁻¹ᵁ U).ι)).app (U.ι ''ᵁ V) ≫
      ((Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι))).app V = _
  simp only [rightSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app]
  simp only [modules_comp_app,Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  simp only [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.restrict_map]
  erw [Category.id_comp, Category.comp_id, ← Functor.map_comp, ← Functor.map_comp]
  congr 1

lemma tensor_pure (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V))))
    (n : N.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V)))) :
    (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U (moduleTensor X M N)).app V
        (pure M N (f ⁻¹ᵁ (U.ι ''ᵁ V)) m n)) =
    pure (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U M).app V m) ((hom f U N).app V n) := by
  rw [hom_app, hom_app, hom_app]
  change (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app _
    ((moduleTensor X M N).val.map _ (pure M N _ m n)) = _
  exact (congrArg (fun t => (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app
    ((f ∣_ U) ⁻¹ᵁ V) t) (pure_restrict M N
      (eqToHom (image_morphismRestrict_preimage f U V)) m n)).trans
    (restrict_pure (f ⁻¹ᵁ U) M N ((f ∣_ U) ⁻¹ᵁ V) _ _)

lemma tensor_square (M N : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (PushforwardTensor.hom f M N) ≫
      (iso f U (moduleTensor X M N)).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom =
    (moduleTensorRestrict U ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N)).hom ≫
      moduleTensorMap (iso f U M).hom (iso f U N).hom ≫
      PushforwardTensor.hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) := by
  apply TensorPure.restrict_hom_ext U
  intro V m n
  change (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
    ((hom f U (moduleTensor X M N)).app V
      ((PushforwardTensor.hom f M N).app (U.ι ''ᵁ V)
        (pure _ _ (U.ι ''ᵁ V) m n))) =
    (PushforwardTensor.hom (f ∣_ U) _ _).app V
      ((moduleTensorMap (iso f U M).hom (iso f U N).hom).app V
        ((moduleTensorRestrict U _ _).hom.app V (pure _ _ (U.ι ''ᵁ V) m n)))
  have hA := congrArg (fun z =>
    (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U (moduleTensor X M N)).app V z))
    (PushforwardTensor.hom_pure f M N (U.ι ''ᵁ V) m n)
  have hB := congrArg (fun z => (PushforwardTensor.hom (f ∣_ U) _ _).app V
    ((moduleTensorMap (iso f U M).hom (iso f U N).hom).app V z))
    (restrict_pure U ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N) V m n)
  have hC := congrArg (fun z => (PushforwardTensor.hom (f ∣_ U) _ _).app V z)
    (map_pure (iso f U M).hom (iso f U N).hom V m n)
  have hD := PushforwardTensor.hom_pure (f ∣_ U)
    (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) V
      ((hom f U M).app V m) ((hom f U N).app V n)
  exact hA.trans ((tensor_pure f U M N V m n).trans ((hB.trans (hC.trans hD)).symm))

@[reassoc] lemma naturality {M N : X.Modules} (a : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward f).map a) ≫
      (iso f U N).hom =
    (iso f U M).hom ≫ (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map a) := by
  ext V x
  change (hom f U N).app V (a.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) x) =
    a.app ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) ((hom f U M).app V x)
  rw [hom_app,hom_app]
  exact (CategoryTheory.congr_fun (a.mapPresheaf.naturality
    (eqToHom (image_morphismRestrict_preimage f U V)).op) x).symm

end PiExponentSeshadri.OpenBaseChange

end

end OAI
