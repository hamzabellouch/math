import OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws
import OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen

namespace OAI

noncomputable section

namespace PiExponentSeshadri.TensorPure

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma assoc_pure (L M N : LineBundle X) (U : X.Opens)
    (l : Γ(L.sheaf,U)) (m : Γ(M.sheaf,U)) (n : Γ(N.sheaf,U)) :
    (lineTensorAssoc L M N).hom.val.app (op U)
      (pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n) =
      pure L.sheaf (M.tensor N).sheaf U l (pure M.sheaf N.sheaf U m n) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let P := L.sheaf.val ⊗ M.sheaf.val
  let Q := M.sheaf.val ⊗ N.sheaf.val
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let a := (lineTensorAssoc L M N)
  let v := ((adj X).unit.app (P ⊗ N.sheaf.val)).app (op U)
    ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)
  have hr : (sheafificationTensorRight P N).hom.val.app (op U) v =
      pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
    have h := (adj X).unit.naturality
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
        ((adj X).unit.app P) (𝟙 N.sheaf.val))
    exact (congrArg (fun q => q.app (op U) ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)) h).symm
  have ha : (F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom).val.app (op U) v =
      ((adj X).unit.app (L.sheaf.val ⊗ Q)).app (op U)
        (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n)) := by
    have h := (adj X).unit.naturality (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom
    exact (congrArg (fun q => q.app (op U) ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)) h).symm
  have hl : (sheafificationTensorLeft Q L).hom.val.app (op U)
      (((adj X).unit.app (L.sheaf.val ⊗ Q)).app (op U)
        (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n))) =
      pure L.sheaf (M.tensor N).sheaf U l (pure M.sheaf N.sheaf U m n) := by
    have h := (adj X).unit.naturality
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
        (𝟙 L.sheaf.val) ((adj X).unit.app Q))
    exact (congrArg (fun q => q.app (op U) (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n))) h).symm
  change a.hom.val.app (op U) _ = _
  have hc : a.hom.val.app (op U) ((sheafificationTensorRight P N).hom.val.app (op U) v) =
      (sheafificationTensorLeft Q L).hom.val.app (op U)
        ((F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom).val.app (op U) v) := by
    change ((sheafificationTensorRight P N).hom ≫ a.hom).val.app (op U) v = _
    change ((sheafificationTensorRight P N).hom ≫
      (sheafificationTensorRight P N).inv ≫
      F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom ≫
      (sheafificationTensorLeft Q L).hom).val.app (op U) v = _
    have hs := (sheafificationTensorRight P N).hom_inv_id_assoc
      (F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom ≫
        (sheafificationTensorLeft Q L).hom)
    exact congrArg (fun q => q.val.app (op U) v) hs
  exact (congrArg (a.hom.val.app (op U)) hr).symm.trans (hc.trans ((congrArg
    ((sheafificationTensorLeft Q L).hom.val.app (op U)) ha).trans hl))

lemma assoc_inv_pure (L M N : LineBundle X) (U : X.Opens)
    (l : Γ(L.sheaf,U)) (m : Γ(M.sheaf,U)) (n : Γ(N.sheaf,U)) :
    (lineTensorAssoc L M N).inv.app U
      (pure L.sheaf (M.tensor N).sheaf U l (pure M.sheaf N.sheaf U m n)) =
      pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
  have h := congrArg ((lineTensorAssoc L M N).inv.app U) (assoc_pure L M N U l m n)
  have hc : (lineTensorAssoc L M N).inv.app U
      ((lineTensorAssoc L M N).hom.val.app (op U)
        (pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n)) =
      pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
    change ((lineTensorAssoc L M N).hom ≫ (lineTensorAssoc L M N).inv).app U _ = _
    rw [Iso.hom_inv_id]
    rfl
  exact h.symm.trans hc

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma unit_inv_apply (M : X.Modules) (U : X.Opens) (m : Γ(M,U)) :
    (moduleTensorUnit M).inv.app U m = pure (O X) M U (1 : Γ(X,U)) m := by
  have h := congrArg ((moduleTensorUnit M).inv.app U) (unit_pure M U (1 : Γ(X,U)) m)
  have hc : (moduleTensorUnit M).inv.app U
      ((moduleTensorUnit M).hom.app U (pure (O X) M U (1 : Γ(X,U)) m)) =
      pure (O X) M U (1 : Γ(X,U)) m := by
    change ((moduleTensorUnit M).hom ≫ (moduleTensorUnit M).inv).app U _ = _
    rw [Iso.hom_inv_id]
    rfl
  exact (congrArg ((moduleTensorUnit M).inv.app U) (one_smul Γ(X,U) m)).symm.trans (h.symm.trans hc)

lemma power_succ_apply {M : X.Modules} (s : O X ⟶ M) (n : ℕ) (U : X.Opens) :
    (powerSection s (n+1)).app U (1 : Γ(X,U)) =
      pure M (modulePow X M n) U (s.app U (1 : Γ(X,U)))
        ((powerSection s n).app U (1 : Γ(X,U))) := by
  change (moduleTensorMap s (modulePowMap s n)).app U
    ((moduleTensorUnit (modulePow X (O X) n)).inv.app U
      ((unitPowerIso n).inv.app U (1 : Γ(X,U)))) = _
  exact (congrArg ((moduleTensorMap s (modulePowMap s n)).app U)
    (unit_inv_apply _ U _)).trans (map_pure _ _ U _ _)

lemma openSection_tensor (M N : X.Modules) (U : X.Opens)
    (s : O U.toScheme ⟶ M.restrict U.ι) (t : O U.toScheme ⟶ N.restrict U.ι) :
    openSectionEquiv (moduleTensor X M N) U
      (tensorSection s t ≫ (moduleTensorRestrict U M N).inv) =
    pure M N U (openSectionEquiv M U s) (openSectionEquiv N U t) := by
  change (moduleTensor X M N).presheaf.map (eqToHom U.ι_image_top.symm).op
    ((moduleTensorRestrict U M N).inv.app ⊤ ((tensorSection s t).app ⊤ (1 : Γ(U.toScheme,⊤)))) = _
  have h := (congrArg ((moduleTensorRestrict U M N).inv.app ⊤)
    (section_apply s t ⊤)).trans (restrict_pure_inv U M N ⊤ _ _)
  exact (congrArg ((moduleTensor X M N).presheaf.map (eqToHom U.ι_image_top.symm).op) h).trans
    (pure_restrict M N (eqToHom U.ι_image_top.symm) _ _)

instance tensorSection_isIso {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N)
    [hs : IsIso s] [ht : IsIso t] : IsIso (tensorSection s t) := by
  exact ((moduleTensorUnit (O X)).symm ≪≫
    moduleTensorIso (@asIso _ _ _ _ s hs) (@asIso _ _ _ _ t ht)).isIso_hom

lemma mixed_value_restrict {M N : X.Modules} (U : X.Opens) (a : O X ⟶ M)
    (b : O U.toScheme ⟶ N.restrict U.ι) (t : O X ⟶ moduleTensor X M N)
    (ht : t.app U (1 : Γ(X,U)) = pure M N U (a.app U (1 : Γ(X,U))) (openSectionEquiv N U b)) :
    restrictSection U.ι t = tensorSection (restrictSection U.ι a) b ≫ (moduleTensorRestrict U M N).inv := by
  apply (openSectionEquiv (moduleTensor X M N) U).injective
  rw [openSectionEquiv_restrict,openSection_tensor,openSectionEquiv_restrict]
  exact ht

lemma mixed_value_open {M N : X.Modules} (U : X.Opens) (a : O X ⟶ M)
    (b : O U.toScheme ⟶ N.restrict U.ι) [IsIso (restrictSection U.ι a)] [IsIso b]
    (t : O X ⟶ moduleTensor X M N)
    (ht : t.app U (1 : Γ(X,U)) = pure M N U (a.app U (1 : Γ(X,U))) (openSectionEquiv N U b)) :
    U ≤ SectionOpens.isoOpen t := by
  have hi : IsIso (restrictSection U.ι t) := by
    rw [mixed_value_restrict U a b t ht]
    infer_instance
  intro x hx
  apply (SectionOpens.mem_isoOpen_iff t x).mpr
  refine ⟨U,hx,?_⟩
  let hu : IsIso (C := U.toScheme.Modules) (Scheme.Modules.restrictUnitIso U.ι).inv :=
    (Scheme.Modules.restrictUnitIso U.ι).isIso_inv
  exact (@isIso_comp_left_iff U.toScheme.Modules _ _ _ _ _ _ hu).mp hi

end PiExponentSeshadri.TensorPure

end

end OAI
