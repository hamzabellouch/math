import OAI.Algebra.Finitistic.Rectification.VertexColumnModels

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.VertexColumnComplex
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
local notation "T" => ThreeVertexAlgebra μ
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule

abbrev vertexColumn (i j : Fin 3) : ModuleCat.{u} Tᵐᵒᵖ ⥤ ModuleCat.{u} Tᵐᵒᵖ :=
  ExternalTensor.Section4.columnFunctor k T (ThreeVertexAlgebra.vertex μ j) ⋙
    BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex μ i)

/-- The diagonal insertion is natural in the original right module. -/
def diagonalNatIso (i : Fin 3) : 𝟭 (ModuleCat.{u} Tᵐᵒᵖ) ≅ vertexColumn μ i i :=
  NatIso.ofComponents (fun N => (BimoduleVertex.diagonalEquiv μ N i).symm.toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro n
    apply Subtype.ext
    change ((BimoduleVertex.diagonalEquiv μ N i).symm (f.hom n)).val =
      ExternalTensor.columnMap k (ThreeVertexAlgebra.vertex μ i) f.hom
        (((BimoduleVertex.diagonalEquiv μ M i).symm n).val)
    rw [VertexColumnModels.diagonal_symm_val,VertexColumnModels.diagonal_symm_val]
    rfl)

/-- On actual complexes, the diagonal vertex is the original complex via its specified insertion. -/
def diagonalComplexIso (i : Fin 3) (D : CochainComplex (ModuleCat.{u} Tᵐᵒᵖ) ℤ) :
    D ≅ ((vertexColumn μ i i).mapHomologicalComplex (.up ℤ)).obj D :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (diagonalNatIso μ i).app (D.X n))
    (fun n m _ => ((diagonalNatIso μ i).hom.naturality (D.d n m)).symm)

/-- Every term of a reverse vertex column is zero, hence the actual complex is zero. -/
theorem reverse_isZero (i j : Fin 3) (hij : i < j)
    (D : CochainComplex (ModuleCat.{u} Tᵐᵒᵖ) ℤ) :
    IsZero (((vertexColumn μ i j).mapHomologicalComplex (.up ℤ)).obj D) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (VertexColumnModels.reverse_zero μ (D.X n) i j hij).elim _ _
end LittleFinitistic.VertexColumnComplex

end

end OAI
