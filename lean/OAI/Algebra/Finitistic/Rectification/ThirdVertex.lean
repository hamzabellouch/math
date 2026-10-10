import OAI.Algebra.Finitistic.Rectification.ThirdVertexFiltration
import OAI.Algebra.Finitistic.Rectification.InducedRectification
import OAI.Algebra.Finitistic.Rectification.FinalGradedAcyclic

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.ThirdVertex
open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)
local notation "s" => ConcreteQuadraticDiagram.quadratic P
abbrev vertexComplex := AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2

theorem filtration_inclusion_quasiIso :
    QuasiIso ((vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H)) := by
  let S := Complex.source0 s D₀ D₁ D₂ f g H
  exact RectificationAcyclic.quasiIso_of_acyclic_quotient (S.map (vertexComplex P))
    (Complex.vertex_shortExact ((s).e₂)
      ((ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition P)).idem 2) S
      (Complex.source0_shortExact s D₀ D₁ D₂ f g H))
    (FinalGradedAcyclic.grade0_vertex2_acyclic P D₀ D₁ D₂ f g)

def iota : D₂ ⟶ (vertexComplex P).obj (Exactness.P s D₀ D₁ D₂ f g H) :=
  (VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 2 D₂).hom ≫
    (vertexComplex P).map (Exactness.i2 s D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H)

theorem iota_quasiIso : QuasiIso (iota P D₀ D₁ D₂ f g H) := by
  let := ThirdVertexFiltration.inclusion_quasiIso P D₀ D₁ D₂ f g
  let := filtration_inclusion_quasiIso P D₀ D₁ D₂ f g H
  let e : D₂ ≅ (vertexComplex P).obj ((columnComplex k (QuadraticEncoding.B P) (s).e₂).obj D₂) :=
    VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 2 D₂
  change QuasiIso (e.hom ≫ (vertexComplex P).map (Exactness.i2 s D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H))
  infer_instance

/-- The final-vertex map is the original e2 tensor insertion followed by the original total inclusion. -/
theorem iota_original : iota P D₀ D₁ D₂ f g H =
    (VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 2 D₂).hom ≫
      (vertexComplex P).map ((Exactness.data s D₀ D₁ D₂ f g).in₂) ≫
      (vertexComplex P).map (InducedRectification.inclusion s D₀ D₁ D₂ f g H) := by
  dsimp only [iota]
  erw [← (vertexComplex P).map_comp (Exactness.i2 s D₀ D₁ D₂ f g)
    (Exactness.i1 s D₀ D₁ D₂ f g H),
    (Exactness.exact_source_filtration s D₀ D₁ D₂ f g H 0).2.2, Functor.map_comp]
  rfl
end LittleFinitistic.ThirdVertex

end

end OAI
