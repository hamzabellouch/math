import OAI.Algebra.Finitistic.Rectification.SecondVertex

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.VertexTotalProperties
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- The actual vertex of a right-projective bimodule remains right-projective. -/
theorem projective (e : B) (he : e*e=e) (M : ModuleCat.{u} (Enveloping k B))
    (hM : Projective ((forgetRight k B).obj M)) :
    Projective ((BimoduleVertex.functor k B e).obj M) := by
  let := hM
  have : Module.Projective Bᵐᵒᵖ (VertexFunctor.restricted (BimoduleVertex.restriction k B) M) :=
    inferInstanceAs (Module.Projective Bᵐᵒᵖ ((forgetRight k B).obj M))
  have := VertexFunctor.projective (BimoduleVertex.restriction k B) (BimoduleVertex.vertex k B e)
      (BimoduleVertex.vertex_idempotent k B e he) (BimoduleVertex.vertex_commute k B e) M
  change Projective (ModuleCat.of Bᵐᵒᵖ
    (VertexFunctor.fixed (BimoduleVertex.restriction k B) (BimoduleVertex.vertex k B e)
      (BimoduleVertex.vertex_commute k B e) M))
  exact ModuleCat.projective_of_categoryTheory_projective (R := Bᵐᵒᵖ) _

variable {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy
  (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

/-- Every actual vertex of the constructed total has projective right-module terms. -/
theorem total_projective (v : Fin 3)
    (h₀ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₂.X n)) (n : ℤ) :
    Projective (((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) v).obj
      (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)).X n) :=
  projective (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) v)
    ((ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition P)).idem v) _
    (InducedRectification.rightTotal_projective (ConcreteQuadraticDiagram.quadratic P)
      D₀ D₁ D₂ f g H h₀ h₁ h₂ n)

theorem total_bounded (v : Fin 3) (lo hi : ℤ)
    (h₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (h₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (h₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n)) :
    ∀ n, n < lo-2 ∨ hi < n → IsZero
      (((AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) v).obj
        (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)).X n) := by
  intro n hn
  exact (BimoduleVertex.functor k (QuadraticEncoding.B P)
    (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) v)).map_isZero
    (InducedRectification.total_bounded (ConcreteQuadraticDiagram.quadratic P)
      D₀ D₁ D₂ f g H lo hi h₀ h₁ h₂ n hn)
end LittleFinitistic.VertexTotalProperties

end

end OAI
