import OAI.Algebra.Finitistic.Rectification.CornerArrowCoordinates
import OAI.Algebra.Finitistic.Rectification.TensorArrowSum

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.AdjacentArrowSum
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
variable (D : CochainComplex (ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ) ℤ)
local notation "T" => ThreeVertexAlgebra μ
local instance : HasFiniteBiproducts (CochainComplex (ModuleCat.{u} Tᵐᵒᵖ) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts
abbrev vertexComplex (v : Fin 3) :=
  (BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex μ v)).mapHomologicalComplex (.up ℤ)

def sourceIso (v : Fin 3) :
    (vertexComplex μ v).obj ((ExternalTensor.Section4.columnComplex k T
      (ThreeVertexAlgebra.vertex μ v)).obj D) ≅
      (TensorComplex.tensorFunctor (k := k) D).obj (ModuleCat.of k k) :=
  (CornerColumnComplex.complexIso μ v v D).symm ≪≫
    (TensorComplex.tensorFunctor (k := k) D).mapIso (CornerSpaces.diagonalEquiv μ v).toModuleIso

def targetIso (v i : Fin 3) (d : ℕ)
    (ξ : CornerSpaces.corner μ v i ≃ₗ[k] QuadraticEncoding.Arrows k d) :
    (vertexComplex μ v).obj ((ExternalTensor.Section4.columnComplex k T
      (ThreeVertexAlgebra.vertex μ i)).obj D) ≅
      (TensorComplex.tensorFunctor (k := k) D).obj (ModuleCat.of k (QuadraticEncoding.Arrows k d)) :=
  (CornerColumnComplex.complexIso μ v i D).symm ≪≫
    (TensorComplex.tensorFunctor (k := k) D).mapIso ξ.toModuleIso

/-- An actual adjacent path family becomes the full arrow basis under corner coordinates. -/
theorem desc_isIso (v i : Fin 3) (d : ℕ)
    (ξ : CornerSpaces.corner μ v i ≃ₗ[k] QuadraticEncoding.Arrows k d)
    (a : Fin (d+1) → ThreeVertexAlgebra μ)
    (ha : ∀ j, a j * ThreeVertexAlgebra.vertex μ i = a j)
    (hc : ∀ j c, ξ (CornerColumnPaths.cornerMap μ v i v (a j) (ha j)
      ((CornerSpaces.diagonalEquiv μ v).symm c)) = c • QuadraticEncoding.basis j) :
    IsIso (biproduct.desc (fun j => (vertexComplex μ v).map
      (ExternalTensor.Section4.path k T (ThreeVertexAlgebra.vertex μ i)
        (ThreeVertexAlgebra.vertex μ v) (a j) (ha j) D))) := by
  let F := TensorComplex.tensorFunctor (k := k) D
  apply TensorArrowSum.desc_isIso_of_coordinates k d F _ _
    (fun _ => sourceIso μ D v) (targetIso μ D v i d ξ)
  intro j
  have hm : ModuleCat.ofHom (CornerSpaces.diagonalEquiv μ v).toLinearMap ≫
      TensorArrowSum.insertion k d j =
      ModuleCat.ofHom (CornerColumnPaths.cornerMap μ v i v (a j) (ha j)) ≫
        ModuleCat.ofHom ξ.toLinearMap := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (TensorArrowSum.insertion k d j).hom ((CornerSpaces.diagonalEquiv μ v) x) =
      ξ (CornerColumnPaths.cornerMap μ v i v (a j) (ha j) x)
    rw [TensorArrowSum.insertion_apply]
    simpa only [LinearEquiv.symm_apply_apply]
      using (hc j ((CornerSpaces.diagonalEquiv μ v) x)).symm
  have hF := congrArg F.map hm
  simp only [Functor.map_comp] at hF
  apply (cancel_epi (CornerColumnComplex.complexIso μ v v D).hom).1
  calc
    _ = F.map (ModuleCat.ofHom (CornerSpaces.diagonalEquiv μ v).toLinearMap) ≫
        F.map (TensorArrowSum.insertion k d j) := by
      change (CornerColumnComplex.complexIso μ v v D).hom ≫
        ((CornerColumnComplex.complexIso μ v v D).inv ≫
          F.map (ModuleCat.ofHom (CornerSpaces.diagonalEquiv μ v).toLinearMap)) ≫
        F.map (TensorArrowSum.insertion k d j) = _
      erw [Category.assoc]
      exact (CornerColumnComplex.complexIso μ v v D).hom_inv_id_assoc _
    _ = F.map (ModuleCat.ofHom (CornerColumnPaths.cornerMap μ v i v (a j) (ha j))) ≫
        F.map (ModuleCat.ofHom ξ.toLinearMap) := hF
    _ = (F.map (ModuleCat.ofHom
          (CornerColumnPaths.cornerMap μ v i v (a j) (ha j))) ≫
        (CornerColumnComplex.complexIso μ v i D).hom) ≫
          (targetIso μ D v i d ξ).hom := by simp [targetIso,F,TensorComplex.tensorFunctor]
    _ = _ := by
      erw [CornerColumnPaths.path_naturality]
      exact Category.assoc _ _ _
end LittleFinitistic.AdjacentArrowSum

end

end OAI
