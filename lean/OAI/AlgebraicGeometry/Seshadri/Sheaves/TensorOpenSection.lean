import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.SectionOpens
import OAI.AlgebraicGeometry.Seshadri.Sheaves.RestrictTensorMap
import OAI.AlgebraicGeometry.Seshadri.Cohomology.MixedLocalExtension

namespace OAI


                                           
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

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
    [IsIso s] [IsIso t] : IsIso (tensorSection s t) := by
  let unitIso : moduleTensor X (O X) (O X) ≅ O X := moduleTensorUnit (O X)
  let tensorMap : moduleTensor X (O X) (O X) ⟶ moduleTensor X M N :=
    moduleTensorMap s t
  have : IsIso tensorMap := moduleTensorMap_isIso (X := X) s t
  change IsIso (unitIso.inv ≫ tensorMap)
  infer_instance

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
  let unitIso : (Scheme.Modules.restrictFunctor U.ι).obj (O X) ≅ O U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  exact (isIso_comp_left_iff unitIso.inv
    ((Scheme.Modules.restrictFunctor U.ι).map t)).mp hi

end
end MaximalSeshadri.TensorPure

end

end OAI
