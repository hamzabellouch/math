import OAI.Algebra.Finitistic.Rectification.CanonicalArrowCompatibility
import OAI.Algebra.Finitistic.Rectification.TotalFinite

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.RectificationLemma
open ExternalTensor.Section4 QuadraticEncoding CanonicalArrowCompatibility
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

/-- The conclusions of the paper's rectification lemma for the explicitly constructed
bimodule complex and original vertex insertion maps. -/
structure Verified (lo hi : ℤ) : Prop where
  bounded : ∀ n, n < lo-2 ∨ hi < n → IsZero
    ((InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H).X n)
  projective : ∀ n, Projective
    ((InducedRectification.rightTotal (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H).X n)
  finite : ∀ n, FiniteDimensional k ((forgetK k (B P)).obj
    ((InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H).X n))
  vertices : ∀ v : Fin 3, ∃ j :
    VertexHomotopyEquivalence.target P D₀ D₁ D₂ f g H v ⟶
    VertexHomotopyEquivalence.source P D₀ D₁ D₂ v,
    Nonempty (Homotopy (VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H v ≫ j) (𝟙 _)) ∧
    Nonempty (Homotopy (j ≫ VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H v) (𝟙 _))
  arrows01 : ∀ a, Nonempty (Homotopy
    (FirstVertex.iota P D₀ D₁ D₂ f g H ≫ arrow01Map P D₀ D₁ D₂ f g H a)
    (f a ≫ SecondVertex.iota P D₀ D₁ D₂ f g H))
  arrows12 : ∀ b, Nonempty (Homotopy
    (SecondVertex.iota P D₀ D₁ D₂ f g H ≫ arrow12Map P D₀ D₁ D₂ f g H b)
    (g b ≫ ThirdVertex.iota P D₀ D₁ D₂ f g H))

/-- Full rectification for arbitrary bounded finite projective input complexes,
using only the assigned relation homotopies. No conclusion about the constructed
P, its vertices, or its arrow homotopies is assumed. -/
theorem rectification (lo hi : ℤ)
    (b₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (b₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (b₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n))
    (p₀ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₀.X n))
    (p₁ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₁.X n))
    (p₂ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₂.X n))
    (f₀ : ∀ n, Module.Finite (B P)ᵐᵒᵖ (D₀.X n))
    (f₁ : ∀ n, Module.Finite (B P)ᵐᵒᵖ (D₁.X n))
    (f₂ : ∀ n, Module.Finite (B P)ᵐᵒᵖ (D₂.X n)) :
    Verified P D₀ D₁ D₂ f g H lo hi := by
  have := QuadraticEncoding.finiteDimensional P
  exact {
    bounded := InducedRectification.total_bounded _ _ _ _ _ _ _ lo hi b₀ b₁ b₂
    projective := InducedRectification.rightTotal_projective _ _ _ _ _ _ _ p₀ p₁ p₂
    finite := induced_total_finite _ _ _ _ _ _ _ f₀ f₁ f₂
    vertices := fun v => VertexHomotopyEquivalence.homotopy_inverse P D₀ D₁ D₂ f g H
      v lo hi b₀ b₁ b₂ p₀ p₁ p₂
    arrows01 := fun a => ⟨CanonicalArrowCompatibility.compatibility01 P D₀ D₁ D₂ f g H a⟩
    arrows12 := fun b => ⟨CanonicalArrowCompatibility.compatibility12 P D₀ D₁ D₂ f g H b⟩ }
end LittleFinitistic.RectificationLemma

end

end OAI
