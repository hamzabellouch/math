import OAI.Algebra.Finitistic.Rectification.SourceFiltrationComplex
import OAI.Algebra.Finitistic.Rectification.ConcreteAdjacentGraded
import OAI.Algebra.Finitistic.Rectification.ZeroLastColumn
import OAI.Algebra.Finitistic.Rectification.ColumnProperties

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace LittleFinitistic.GradedVertexAcyclic

theorem acyclic_of_iso {C : Type*} [Category C] [Abelian C]
    {X Y : CochainComplex C ℤ} (e : X ≅ Y) (hY : Y.Acyclic) : X.Acyclic := by
  intro n
  rw [exactAt_iff_isZero_homology]
  exact ((homologyFunctor C (.up ℤ) n).mapIso e).isZero_iff.mpr (hY n).isZero_homology

open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P

/-- The actual source-one quotient is the adjacent-arrow cone after taking vertex two. -/
def grade1VertexIso :
    (AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2).obj
      (Exactness.G1 s D₀ D₁ D₂ f g) ≅
    mappingCone ((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2).map
      (ConcreteAdjacentGraded.arrow12Sum P D₁)) :=
  (AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2).mapIso
    (grade1ConeIso (Exactness.data s D₀ D₁ D₂ f g)).symm ≪≫
  mappingCone.mapHomologicalComplexIso (pGrade1 (Exactness.data s D₀ D₁ D₂ f g))
    (BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) 2))

theorem grade1_vertex2_acyclic :
    ((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2).obj
      (Exactness.G1 s D₀ D₁ D₂ f g)).Acyclic :=
  acyclic_of_iso (grade1VertexIso P D₀ D₁ D₂ f g)
    (ConcreteAdjacentGraded.vertex2_cone_acyclic P D₁)

/-- The relation column of the actual source-zero quotient vanishes at vertex one. -/
theorem relationColumn_vertex1_zero :
    IsZero ((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 1).obj
      (Exactness.data s D₀ D₁ D₂ f g).L₂) := by
  let F := AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 1
  change IsZero (F.obj (⨁ fun _ : RelationBasisCoefficients.RelationIndex P =>
    (columnComplex k T (s).e₂).obj D₀))
  apply (F.mapBiproduct _).isZero_iff.mpr
  exact sum_isZero _ (fun _ =>
    VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 1 2 (by decide) D₀)

/-- The actual source-zero quotient at vertex one is the first adjacent-arrow cone. -/
def grade0Vertex1Iso :
    (AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 1).obj
      (Exactness.G0 s D₀ D₁ D₂ f g) ≅
    mappingCone ((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 1).map
      (ConcreteAdjacentGraded.arrow01Sum P D₀)) :=
  ZeroLastColumn.mappedTotalIso (p0 (Exactness.data s D₀ D₁ D₂ f g))
    (q0 (Exactness.data s D₀ D₁ D₂ f g)) (h0 (Exactness.data s D₀ D₁ D₂ f g))
    (BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) 1))
    (relationColumn_vertex1_zero P D₀ D₁ D₂ f g)

theorem grade0_vertex1_acyclic :
    ((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 1).obj
      (Exactness.G0 s D₀ D₁ D₂ f g)).Acyclic :=
  acyclic_of_iso (grade0Vertex1Iso P D₀ D₁ D₂ f g)
    (ConcreteAdjacentGraded.vertex1_cone_acyclic P D₀)
end LittleFinitistic.GradedVertexAcyclic

end

end OAI
