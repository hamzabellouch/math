import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorDivision
import OAI.AlgebraicGeometry.Seshadri.Sheaves.ModuleLocal

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma moduleTensorIso_inv {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    (moduleTensorIso e f).inv = moduleTensorMap e.inv f.inv := rfl

def tensorInclusion (J M : LineBundle X) (ι : J.sheaf ⟶ O X) :
    (J.tensor M).sheaf ⟶ M.sheaf :=
  moduleTensorMap ι (𝟙 M.sheaf) ≫ (moduleTensorUnit M.sheaf).hom

lemma tensor_inclusion_framed (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.Opens) (e : J.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (tensorFrame J M U e f).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (tensorInclusion J M ι) ≫ f.hom =
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom) ≫ (tensorUnitTwist M U f).inv := by
  let restrictionFunctor : X.Modules ⥤ U.toScheme.Modules :=
    Scheme.Modules.restrictFunctor U.ι
  let unitRestriction : restrictionFunctor.obj (O X) ≅ O U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  let sourceUnit : moduleTensor X (O X) M.sheaf ≅ M.sheaf :=
    moduleTensorUnit M.sheaf
  let targetUnit : moduleTensor U.toScheme (O U.toScheme) (O U.toScheme) ≅
      O U.toScheme := moduleTensorUnit (O U.toScheme)
  let sourceRestriction : restrictionFunctor.obj (moduleTensor X J.sheaf M.sheaf) ≅
      moduleTensor U.toScheme (restrictionFunctor.obj J.sheaf)
        (restrictionFunctor.obj M.sheaf) := moduleTensorRestrict U J.sheaf M.sheaf
  let targetRestriction : restrictionFunctor.obj (moduleTensor X (O X) M.sheaf) ≅
      moduleTensor U.toScheme (restrictionFunctor.obj (O X))
        (restrictionFunctor.obj M.sheaf) := moduleTensorRestrict U (O X) M.sheaf
  let tensorMap : moduleTensor X J.sheaf M.sheaf ⟶ moduleTensor X (O X) M.sheaf :=
    moduleTensorMap ι (𝟙 M.sheaf)
  let inclusion : moduleTensor X J.sheaf M.sheaf ⟶ M.sheaf := tensorInclusion J M ι
  let frame : restrictionFunctor.obj (moduleTensor X J.sheaf M.sheaf) ≅
      O U.toScheme := tensorFrame J M U e f
  let twist : O U.toScheme ≅ O U.toScheme := tensorUnitTwist M U f
  let scalar : O U.toScheme ⟶ O U.toScheme :=
    e.inv ≫ restrictionFunctor.map ι ≫ unitRestriction.hom
  have inclusion_eq : inclusion = tensorMap ≫ sourceUnit.hom := rfl
  have naturality : restrictionFunctor.map tensorMap ≫ targetRestriction.hom =
      sourceRestriction.hom ≫ moduleTensorMap (restrictionFunctor.map ι)
        (𝟙 (restrictionFunctor.obj M.sheaf)) := by
    have naturality' : restrictionFunctor.map tensorMap ≫ targetRestriction.hom =
        sourceRestriction.hom ≫ moduleTensorMap (restrictionFunctor.map ι)
          (restrictionFunctor.map (𝟙 M.sheaf)) :=
      moduleTensorRestrict_natural U ι (𝟙 M.sheaf)
    simpa only [restrictionFunctor.map_id] using naturality'
  change frame.inv ≫ restrictionFunctor.map inclusion ≫ f.hom = scalar ≫ twist.inv
  apply (cancel_mono twist.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have frame_inv : frame.inv =
      (targetUnit.inv ≫ moduleTensorMap (X := U.toScheme) e.inv f.inv) ≫
        sourceRestriction.inv := rfl
  have twist_hom : twist.hom = f.inv ≫
      restrictionFunctor.map sourceUnit.inv ≫ targetRestriction.hom ≫
      moduleTensorMap unitRestriction.hom f.hom ≫ targetUnit.hom := rfl
  rw [frame_inv, twist_hom]
  rw [inclusion_eq, restrictionFunctor.map_comp]
  simp only [Category.assoc, f.hom_inv_id_assoc]
  rw [← restrictionFunctor.map_comp_assoc sourceUnit.hom sourceUnit.inv,
    sourceUnit.hom_inv_id,
    restrictionFunctor.map_id, Category.id_comp]
  rw [← Category.assoc (restrictionFunctor.map tensorMap), naturality]
  simp only [Category.assoc, sourceRestriction.inv_hom_id_assoc]
  rw [← Category.assoc (moduleTensorMap (X := U.toScheme) e.inv f.inv),
    ← moduleTensorMap_comp (X := U.toScheme), Category.comp_id,
    ← Category.assoc (moduleTensorMap (X := U.toScheme) _ _),
    ← moduleTensorMap_comp (X := U.toScheme), f.inv_hom_id]
  have hscalar : moduleTensorMap scalar (𝟙 (O U.toScheme)) ≫ targetUnit.hom =
      targetUnit.hom ≫ scalar := by
    exact (moduleTensorUnit_scalar (X := U.toScheme) scalar (𝟙 (O U.toScheme))).trans
      (congrArg (fun morphism : O U.toScheme ⟶ O U.toScheme =>
        targetUnit.hom ≫ morphism) (Category.comp_id scalar))
  rw [Category.assoc e.inv, hscalar, targetUnit.inv_hom_id_assoc]

theorem tensorInclusion_mono (J M : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι] :
    Mono (tensorInclusion J M ι) := by
  apply ModuleLocal.mono_of_local
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U.1,hx,?_⟩
  have : CategoryTheory.Limits.PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor U.1.ι) := by
    have : CategoryTheory.Limits.PreservesFiniteLimits
        (Scheme.Modules.restrictFunctor U.1.ι ⋙ Scheme.Modules.toPresheaf U.1.toScheme) := by
      change CategoryTheory.Limits.PreservesFiniteLimits
        (Scheme.Modules.toPresheaf X ⋙ (Functor.whiskeringLeft _ _ _).obj U.1.ι.opensFunctor.op)
      have : CategoryTheory.Limits.PreservesFiniteLimits
          (Scheme.Modules.toPresheaf X) := inferInstance
      have : CategoryTheory.Limits.PreservesFiniteLimits
          ((Functor.whiskeringLeft _ _ Ab).obj U.1.ι.opensFunctor.op) := inferInstance
      exact CategoryTheory.Limits.comp_preservesFiniteLimits _ _
    exact CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves _
      (Scheme.Modules.toPresheaf U.1.toScheme)
  have hm : Mono ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom) := by
    let restrictionFunctor : X.Modules ⥤ U.1.toScheme.Modules :=
      Scheme.Modules.restrictFunctor U.1.ι
    let unitRestriction : restrictionFunctor.obj (O X) ≅ O U.1.toScheme :=
      Scheme.Modules.restrictUnitIso U.1.ι
    let twist : O U.1.toScheme ≅ O U.1.toScheme := tensorUnitTwist M U.1 f
    have restricted_mono : Mono (restrictionFunctor.map ι) := inferInstance
    have scalar_mono : Mono ((e.inv ≫ restrictionFunctor.map ι ≫ unitRestriction.hom) ≫
        twist.inv) := inferInstance
    exact (congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme => Mono morphism)
      (tensor_inclusion_framed J M ι U.1 e f)).mpr scalar_mono
  exact (mono_comp_iff_of_mono _ f.hom).mp
    ((mono_comp_iff_of_isIso (tensorFrame J M U.1 e f).inv _).mp hm)

lemma tensor_inclusion_ideal (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom))} =
    Ideal.span {U.1.topIso.hom (endValue (e.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  let scalar : O U.1.toScheme ⟶ O U.1.toScheme := e.inv ≫
    (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom
  let twist : O U.1.toScheme ≅ O U.1.toScheme := tensorUnitTwist M U.1 f
  have framed : (tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom =
      scalar ≫ twist.inv := tensor_inclusion_framed J M ι U.1 e f
  refine (congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme =>
    Ideal.span {U.1.topIso.hom (endValue morphism)}) framed).trans ?_
  change Ideal.span {U.1.topIso.hom (endValue (scalar ≫ twist.inv))} =
    Ideal.span {U.1.topIso.hom (endValue scalar)}
  rw [endValue_comp, map_mul, ← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue twist.inv) :=
    (end_isIso_iff twist.inv).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom), Ideal.mul_top]

end
end MaximalSeshadri.Geometry

end

end OAI
