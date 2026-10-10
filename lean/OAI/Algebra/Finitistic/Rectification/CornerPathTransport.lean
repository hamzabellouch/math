import OAI.Algebra.Finitistic.Rectification.AdjacentArrowSum
import OAI.Algebra.Finitistic.Encoding.RelationMatrixSequence

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.CornerPathTransport
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
variable (D : CochainComplex (ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ) ℤ)
local notation "T" => ThreeVertexAlgebra μ

def coordinateIso (v i : Fin 3) {M : Type u} [AddCommGroup M] [Module k M]
    (ξ : CornerSpaces.corner μ v i ≃ₗ[k] M) :
    (AdjacentArrowSum.vertexComplex μ v).obj ((ExternalTensor.Section4.columnComplex k T
      (ThreeVertexAlgebra.vertex μ i)).obj D) ≅
      (TensorComplex.tensorFunctor (k := k) D).obj (ModuleCat.of k M) :=
  (CornerColumnComplex.complexIso μ v i D).symm ≪≫
    (TensorComplex.tensorFunctor (k := k) D).mapIso ξ.toModuleIso

/-- Coordinate transport preserves each actual path map, before taking any finite sum. -/
theorem path_square (v i j : Fin 3) {M N : Type u}
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (ξ : CornerSpaces.corner μ v j ≃ₗ[k] M)
    (η : CornerSpaces.corner μ v i ≃ₗ[k] N)
    (a : T) (ha : a * ThreeVertexAlgebra.vertex μ i = a)
    (f : M →ₗ[k] N)
    (hc : ∀ x, η (CornerColumnPaths.cornerMap μ v i j a ha x) = f (ξ x)) :
    (coordinateIso μ D v j ξ).hom ≫ (TensorComplex.tensorFunctor (k := k) D).map
      (ModuleCat.ofHom f) =
    (AdjacentArrowSum.vertexComplex μ v).map
      (ExternalTensor.Section4.path k T (ThreeVertexAlgebra.vertex μ i)
        (ThreeVertexAlgebra.vertex μ j) a ha D) ≫ (coordinateIso μ D v i η).hom := by
  let F := TensorComplex.tensorFunctor (k := k) D
  have hm : ModuleCat.ofHom ξ.toLinearMap ≫ ModuleCat.ofHom f =
      ModuleCat.ofHom (CornerColumnPaths.cornerMap μ v i j a ha) ≫
        ModuleCat.ofHom η.toLinearMap := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun x => (hc x).symm)
  have hF := congrArg F.map hm
  simp only [Functor.map_comp] at hF
  apply (cancel_epi (CornerColumnComplex.complexIso μ v j D).hom).1
  calc
    _ = F.map (ModuleCat.ofHom ξ.toLinearMap) ≫ F.map (ModuleCat.ofHom f) := by
      change (CornerColumnComplex.complexIso μ v j D).hom ≫
        ((CornerColumnComplex.complexIso μ v j D).inv ≫
          F.map (ModuleCat.ofHom ξ.toLinearMap)) ≫ F.map (ModuleCat.ofHom f) = _
      erw [Category.assoc]
      exact (CornerColumnComplex.complexIso μ v j D).hom_inv_id_assoc _
    _ = F.map (ModuleCat.ofHom (CornerColumnPaths.cornerMap μ v i j a ha)) ≫
        F.map (ModuleCat.ofHom η.toLinearMap) := hF
    _ = (F.map (ModuleCat.ofHom
          (CornerColumnPaths.cornerMap μ v i j a ha)) ≫
        (CornerColumnComplex.complexIso μ v i D).hom) ≫
          (coordinateIso μ D v i η).hom := by simp [coordinateIso,F,TensorComplex.tensorFunctor]
    _ = _ := by
      erw [CornerColumnPaths.path_naturality]
      exact Category.assoc _ _ _
end LittleFinitistic.CornerPathTransport

end

end OAI
