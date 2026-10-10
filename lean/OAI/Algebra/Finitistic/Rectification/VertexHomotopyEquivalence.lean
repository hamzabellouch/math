import OAI.Algebra.Finitistic.Rectification.ThirdVertex
import OAI.Algebra.Finitistic.Rectification.VertexTotalProperties

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.VertexHomotopyEquivalence
open ExternalTensor.Section4
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

abbrev source (v : Fin 3) : RightComplex (QuadraticEncoding.B P) :=
  Fin.cases D₀ (Fin.cases D₁ (fun _ => D₂)) v
abbrev target (v : Fin 3) : RightComplex (QuadraticEncoding.B P) :=
  (AdjacentArrowSum.vertexComplex (QuadraticEncoding.composition P) v).obj
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)

def iota (v : Fin 3) : source P D₀ D₁ D₂ v ⟶ target P D₀ D₁ D₂ f g H v := by
  refine Fin.cases (FirstVertex.iota P D₀ D₁ D₂ f g H)
    (Fin.cases (SecondVertex.iota P D₀ D₁ D₂ f g H) ?_) v
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact ThirdVertex.iota P D₀ D₁ D₂ f g H

/-- All three original vertex insertions are quasi-isomorphisms. -/
theorem iota_quasiIso (v : Fin 3) : QuasiIso (iota P D₀ D₁ D₂ f g H v) := by
  fin_cases v
  · let := FirstVertex.iota_isIso P D₀ D₁ D₂ f g H
    change QuasiIso (FirstVertex.iota P D₀ D₁ D₂ f g H)
    infer_instance
  · exact SecondVertex.iota_quasiIso P D₀ D₁ D₂ f g H
  · exact ThirdVertex.iota_quasiIso P D₀ D₁ D₂ f g H

/-- The actual vertex insertions have chain-map inverses and both homotopies.
Only the boundedness and projectivity of the chosen chain representatives are inputs. -/
theorem homotopy_inverse (v : Fin 3) (lo hi : ℤ)
    (b₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (b₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (b₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n))
    (p₀ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₀.X n))
    (p₁ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₁.X n))
    (p₂ : ∀ n, Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ (D₂.X n)) :
    ∃ j : target P D₀ D₁ D₂ f g H v ⟶ source P D₀ D₁ D₂ v,
      Nonempty (Homotopy (iota P D₀ D₁ D₂ f g H v ≫ j) (𝟙 _)) ∧
      Nonempty (Homotopy (j ≫ iota P D₀ D₁ D₂ f g H v) (𝟙 _)) := by
  have : (source P D₀ D₁ D₂ v).IsStrictlyLE hi := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    fin_cases v
    · exact b₀ n (Or.inr hn)
    · exact b₁ n (Or.inr hn)
    · exact b₂ n (Or.inr hn)
  have : (target P D₀ D₁ D₂ f g H v).IsStrictlyLE hi := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact VertexTotalProperties.total_bounded P D₀ D₁ D₂ f g H v lo hi b₀ b₁ b₂ n (Or.inr hn)
  have (n : ℤ) : Projective ((source P D₀ D₁ D₂ v).X n) := by
    fin_cases v
    · change Projective (D₀.X n)
      let := p₀ n
      exact ModuleCat.projective_of_categoryTheory_projective (D₀.X n)
    · change Projective (D₁.X n)
      let := p₁ n
      exact ModuleCat.projective_of_categoryTheory_projective (D₁.X n)
    · change Projective (D₂.X n)
      let := p₂ n
      exact ModuleCat.projective_of_categoryTheory_projective (D₂.X n)
  have (n : ℤ) : Projective ((target P D₀ D₁ D₂ f g H v).X n) :=
    VertexTotalProperties.total_projective P D₀ D₁ D₂ f g H v p₀ p₁ p₂ n
  let := iota_quasiIso P D₀ D₁ D₂ f g H v
  exact RectificationAcyclic.bounded_projective_homotopy_inverse
    (iota P D₀ D₁ D₂ f g H v) hi
end LittleFinitistic.VertexHomotopyEquivalence

end

end OAI
