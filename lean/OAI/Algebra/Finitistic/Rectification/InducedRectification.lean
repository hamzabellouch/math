import Mathlib.Algebra.Category.ModuleCat.Biproducts
import OAI.Algebra.Finitistic.Rectification.InducedDiagram
import OAI.Algebra.Finitistic.Rectification.ColumnProperties
import OAI.Algebra.Finitistic.Rectification.RectificationTotal

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.InducedRectification
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- The actual three-column induced bimodule complex of Section 4. -/
def total : BiComplex k B :=
  RectificationTotal.total (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g)
    (nullHomotopy s D₀ D₁ D₂ f g H)

/-- Its right-module restriction, retaining the original bimodule construction. -/
def rightTotal : RightComplex B :=
  ((forgetRight k B).mapHomologicalComplex (.up ℤ)).obj (total s D₀ D₁ D₂ f g H)

theorem total_bounded (lo hi : ℤ)
    (h₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (h₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (h₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n)) :
    ∀ n, n < lo-2 ∨ hi < n → IsZero ((total s D₀ D₁ D₂ f g H).X n) := by
  have hc := columns_bounded s D₀ D₁ D₂ f g lo hi h₀ h₁ h₂
  exact RectificationTotal.total_bounded _ _ _ lo hi
    (fun n hn => (hc n hn).1) (fun n hn => (hc n hn).2.1)
    (fun n hn => (hc n hn).2.2)

/-- Termwise projectivity holds for the actual right restriction of the total. -/
theorem rightTotal_projective
    (h₀ : ∀ n, Module.Projective Bᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Projective Bᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Projective Bᵐᵒᵖ (D₂.X n)) :
    ∀ n, Projective ((rightTotal s D₀ D₁ D₂ f g H).X n) := by
  have hc := columns_right_projective s D₀ D₁ D₂ f g h₀ h₁ h₂
  exact RectificationTotal.total_projective_after _ _ _ (forgetRight k B)
    (fun n => (hc n).1) (fun n => (hc n).2.1) (fun n => (hc n).2.2)

/-- The entire zero column has its original chain inclusion. -/
def inclusion : L0Prime s D₀ D₁ D₂ f g ⟶ total s D₀ D₁ D₂ f g H :=
  RectificationTotal.inclusion _ _ _

/-- The prescribed first boundary becomes null-homotopic in the actual total. -/
def boundaryHomotopy : Homotopy
    (p s D₀ D₁ D₂ f g ≫ inclusion s D₀ D₁ D₂ f g H) 0 :=
  RectificationTotal.boundaryHomotopy _ _ _
end LittleFinitistic.InducedRectification

end

end OAI
