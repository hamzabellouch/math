import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorPure

namespace OAI


                                            
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry

variable {X Y : Scheme.{0}}

lemma sheafify_restrict_unit (f : X ⟶ Y) [IsOpenImmersion f]
    (P : PresheafOfModules Y.ringCatSheaf.obj) :
    (modulePresheafRestrict f).map ((adj Y).unit.app P) ≫
      ((moduleSheafificationRestrict f).hom.app P).val =
    (adj X).unit.app ((modulePresheafRestrict f).obj P) := by
  let a := adj Y
  let b := Scheme.Modules.restrictAdjunction f
  let c := modulePresheafRestrictAdjunction f
  let d := adj X
  apply (c.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := c.unit_naturality (a.unit.app P)
  erw [← Category.assoc, hn]
  have he := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b) (c.comp d) P
  erw [Adjunction.comp_unit_app a b P, Adjunction.comp_unit_app c d P] at he
  exact he

local instance restrictedSectionModule (U : X.Opens) (M : X.Modules)
    (V : U.toScheme.Opens) :
    Module Γ(U.toScheme, V) (((modulePresheafRestrict U.ι).obj M.val).obj (op V)) :=
  (((modulePresheafRestrict U.ι).obj M.val).obj (op V)).isModule

lemma presheaf_restrict_pure (U : X.Opens) (M N : X.Modules)
    (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    ((modulePresheafTensorRestrict U M.val N.val).hom.app (op V)).hom
      (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n) = (show ((modulePresheafRestrict U.ι).obj M.val).obj (op V) from m) ⊗ₜ[Γ(U.toScheme,V)]
      (show ((modulePresheafRestrict U.ι).obj N.val).obj (op V) from n) := by
  rfl

lemma restrict_pure (U : X.Opens) (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    (moduleTensorRestrict U M N).hom.app V
      (pure M N (U.ι ''ᵁ V) m n) =
      pure (M.restrict U.ι) (N.restrict U.ι) V m n := by
  have h := sheafify_restrict_unit U.ι (presheaf M N)
  have h' := congrArg (fun q => q.app (op V) (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) h
  have hn := (adj U.toScheme).unit.naturality
    (modulePresheafTensorRestrict U M.val N.val).hom
  have hn' := congrArg (fun q => q.app (op V) (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) hn
  change (((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
    (modulePresheafTensorRestrict U M.val N.val).hom).val.app (op V))
    (((moduleSheafificationRestrict U.ι).hom.app (presheaf M N)).val.app (op V)
      (pure M N (U.ι ''ᵁ V) m n)) = _
  simp only [PresheafOfModules.comp_app] at h' hn'
  change (((moduleSheafificationRestrict U.ι).hom.app (presheaf M N)).val.app (op V))
    (pure M N (U.ι ''ᵁ V) m n) = _ at h'
  rw [h']
  refine hn'.symm.trans ?_
  change (((adj U.toScheme).unit.app (presheaf (M.restrict U.ι) (N.restrict U.ι))).app (op V))
    (((modulePresheafTensorRestrict U M.val N.val).hom.app (op V))
      (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) = _
  exact congrArg (fun t => (((adj U.toScheme).unit.app
    (presheaf (M.restrict U.ι) (N.restrict U.ι))).app (op V)) t)
      (presheaf_restrict_pure U M N V m n)

end
end MaximalSeshadri.TensorPure

end

end OAI
