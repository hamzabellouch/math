import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.Supplemental
import OAI.GroupTheory.SimpleAmenable.Configurations.TrajectoryCoordinates

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory AlgebraicTopology
open scoped BigOperators TensorProduct
namespace SimpleAmenable.PolygonObject.LabelledStage
open Labelled IntervalBar.Diagram FreeChains

attribute [local instance 1200] Rep.hV2 Representation.instModuleAsModule TensorProduct.instModule
variable {a n : ℕ} {K : Type} [AddCommGroup K]
noncomputable def coefficientDifferential (a n : ℕ) (K : Type) [AddCommGroup K] :
    Coefficients a (n+1) K →ₗ[ℤ] Coefficients a n K :=
  ∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) • reindexCoefficients (a:=a) (K:=K) (faceFunctor i)
lemma chainCoordinates_d :
    (chainCoordinates a n K).toLinearMap.comp (coefficientDifferential a n K) =
      (groupHomology.inhomogeneousChains.d (SquareStep.coefficientRep a K) n).hom.comp
        (chainCoordinates a (n+1) K).toLinearMap := by
  classical
  apply Finsupp.lhom_ext'
  intro l
  apply LinearMap.ext
  intro v
  change chainCoordinates a n K (coefficientDifferential a n K (Finsupp.single l v)) =
    groupHomology.inhomogeneousChains.d (SquareStep.coefficientRep a K) n
      (chainCoordinates a (n+1) K (Finsupp.single l v))
  simp only [coefficientDifferential,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,chainCoordinates_single]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,chainCoordinates_zero_face,Fin.val_succ,
    chainCoordinates_succ_face]
  erw [one_smul]
  exact (groupHomology.inhomogeneousChains.d_single (A:=SquareStep.coefficientRep a K)
    n (signedLabelEquiv (n+1) l) ((BooleanStep.tensorEquiv (a:=a) (K:=K)).symm v)).symm
noncomputable def trajectoryRep (a j : ℕ) :=
  @SquareStep.coefficientRep a (Stage.K j) inferInstance (AddCommGroup.toIntModule _)
noncomputable def trajectoryRow (a j : ℕ) : SimplicialObject (ModuleCat ℤ) :=
  RestrictedNerve.stringBarRows (positionalProperty a) ⋙ SSet.homologyFunctor Z j
noncomputable def rowCoordinateIso (a n j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    (trajectoryRow a j).obj (Opposite.op (SimplexCategory.mk n)) ≅
      (groupHomology.inhomogeneousChains (trajectoryRep a j)).X n := by
  refine stringCoefficientIso a n j hj hj5 ≪≫ ?_
  exact (chainCoordinates a n (Stage.K j)).toModuleIso
lemma trajectoryRow_face (a n j : ℕ) (i : Fin (n+2)) :
    (trajectoryRow a j).δ i =
      SSet.homologyMap (bar₃Map (stringReindex (a:=a) (faceFunctor i))) Z j := rfl
lemma trajectoryRow_d (a n j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    (AlternatingFaceMapComplex.obj (trajectoryRow a j)).d (n+1) n ≫
      (stringCoefficientIso a n j hj hj5).hom =
    (stringCoefficientIso a (n+1) j hj hj5).hom ≫
      ModuleCat.ofHom (coefficientDifferential a n (Stage.K j)) := by
  rw [AlternatingFaceMapComplex.obj_d_eq]
  change (∑ index : Fin (n+2), (-1:ℤ)^(index:ℕ) •
      SSet.homologyMap (bar₃Map (stringReindex (a:=a) (faceFunctor index))) Z j) ≫
      (stringCoefficientIso a n j hj hj5).hom =
    (stringCoefficientIso a (n+1) j hj hj5).hom ≫
      ModuleCat.ofHom (coefficientDifferential a n (Stage.K j))
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,
    stringCoefficientIso_reindex]
  apply ModuleCat.hom_ext
  ext x
  simp only [coefficientDifferential,ModuleCat.hom_sum,ModuleCat.hom_zsmul,
    ModuleCat.hom_comp,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,ModuleCat.hom_ofHom]
noncomputable def trajectoryChainIso (a j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    AlternatingFaceMapComplex.obj (trajectoryRow a j) ≅
      groupHomology.inhomogeneousChains (trajectoryRep a j) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => rowCoordinateIso a n j hj hj5) ?_
  rintro n m rfl
  symm
  change _ ≫ (stringCoefficientIso a m j hj hj5).hom ≫
      ModuleCat.ofHom (chainCoordinates a m (Stage.K j)).toLinearMap =
    ((stringCoefficientIso a (m+1) j hj hj5).hom ≫
      ModuleCat.ofHom (chainCoordinates a (m+1) (Stage.K j)).toLinearMap) ≫ _
  erw [←Category.assoc,trajectoryRow_d,Category.assoc,groupHomology.inhomogeneousChains.d_def]
  apply ModuleCat.hom_ext
  exact congrArg
    (fun linear => LinearMap.comp linear (stringCoefficientIso a (m+1) j hj hj5).hom.hom)
    (chainCoordinates_d (a:=a) (n:=m) (K:=Stage.K j))
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
