import OAI.Algebra.Finitistic.Rectification.VertexColumnComplex
import OAI.Algebra.Finitistic.Rectification.ZeroColumnTotal
import OAI.Algebra.Finitistic.Rectification.InducedRectification
import OAI.Algebra.Finitistic.Localization.ConcreteQuadraticDiagram

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.VertexZeroTotal
open ExternalTensor.Section4
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
local notation "B" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
abbrev vertexFunctor := BimoduleVertex.functor k (QuadraticEncoding.B P)
  (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) 0)

/-- Actual column terms vanish at vertex zero when their supporting vertex is positive. -/
theorem column_zero (j : Fin 3) (hj : 0 < j) (D : RightComplex (QuadraticEncoding.B P)) (n : ℤ) :
    IsZero ((vertexFunctor P).obj
      (((columnComplex k B (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) j)).obj D).X n)) := by
  exact (HomologicalComplex.eval _ _ n).map_isZero
    (VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 0 j hj D)

variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))

/-- Both higher columns of the constructed total vanish at the first vertex. -/
theorem higher_zero (n : ℤ) :
    IsZero ((vertexFunctor P).obj ((L1Prime s D₀ D₁ D₂ f g).X n)) ∧
    IsZero ((vertexFunctor P).obj ((L2Prime s D₀ D₁ D₂ f g).X n)) := by
  let G := HomologicalComplex.eval (ModuleCat.{u} (Enveloping k B)) (.up ℤ) n ⋙ vertexFunctor P
  let := preservesBinaryBiproducts_of_preservesBiproducts G
  constructor
  · change IsZero (G.obj ((⨁ fun _ : Fin (d+1) =>
      (columnComplex k B (s).e₁).obj D₀) ⊞ (⨁ fun _ : Fin (d+1) =>
      (columnComplex k B (s).e₂).obj D₁)))
    apply (G.mapBiprod _ _).isZero_iff.mpr
    rw [biprod_isZero_iff]
    constructor
    · apply (G.mapBiproduct _).isZero_iff.mpr
      exact sum_isZero _ (fun _ => column_zero P 1 (by decide) D₀ n)
    · apply (G.mapBiproduct _).isZero_iff.mpr
      exact sum_isZero _ (fun _ => column_zero P 2 (by decide) D₁ n)
  · change IsZero (G.obj (⨁ fun _ : RelationBasisCoefficients.RelationIndex P =>
      (columnComplex k B (s).e₂).obj D₀))
    apply (G.mapBiproduct _).isZero_iff.mpr
    exact sum_isZero _ (fun _ => column_zero P 2 (by decide) D₀ n)

/-- At vertex zero, the original zero-column inclusion in the actual total is an isomorphism. -/
theorem inclusion_isIso (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0) :
    IsIso (((vertexFunctor P).mapHomologicalComplex (.up ℤ)).map
      (InducedRectification.inclusion s D₀ D₁ D₂ f g H)) :=
  ZeroColumnTotal.mapped_inclusion_isIso _ _ _ (vertexFunctor P)
    (fun n => (higher_zero P D₀ D₁ D₂ f g n).1)
    (fun n => (higher_zero P D₀ D₁ D₂ f g n).2)
end LittleFinitistic.VertexZeroTotal

end

end OAI
