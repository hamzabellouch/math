import OAI.Algebra.Finitistic.Rectification.GradedVertexAcyclic

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.ThirdVertexFiltration
open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "s" => ConcreteQuadraticDiagram.quadratic P
abbrev vertexComplex := AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) 2

/-- The original deepest source-filtration inclusion is a quasi-isomorphism at vertex two. -/
theorem inclusion_quasiIso :
    QuasiIso ((vertexComplex P).map (Exactness.i2 s D₀ D₁ D₂ f g)) := by
  let S := Complex.source1 s D₀ D₁ D₂ f g
  exact RectificationAcyclic.quasiIso_of_acyclic_quotient (S.map (vertexComplex P))
    (Complex.vertex_shortExact ((s).e₂)
      ((ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition P)).idem 2) S
      (Complex.source1_shortExact s D₀ D₁ D₂ f g))
    (GradedVertexAcyclic.grade1_vertex2_acyclic P D₀ D₁ D₂ f g)
end LittleFinitistic.ThirdVertexFiltration

end

end OAI
