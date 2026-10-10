import OAI.Algebra.Finitistic.Bimodule.BimoduleDerivedInterval

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)
variable (h₀ : ∀ n, Module.Projective Bᵐᵒᵖ (D₀.X n))
variable (h₁ : ∀ n, Module.Projective Bᵐᵒᵖ (D₁.X n))
variable (h₂ : ∀ n, Module.Projective Bᵐᵒᵖ (D₂.X n))

include h₀ h₁ h₂ in
/-- The fixed native rectification supplies the precise projectivity required by the frozen total theorem. -/
theorem induced_term_projective (n : ℤ) : Module.Projective Bᵐᵒᵖ
    (ComplexTensor.rightTerm k B (right k B
      (InducedRectification.total s D₀ D₁ D₂ f g H)) n) := by
  let := InducedRectification.rightTotal_projective s D₀ D₁ D₂ f g H h₀ h₁ h₂ n
  exact inferInstanceAs (Module.Projective Bᵐᵒᵖ
    ((InducedRectification.rightTotal s D₀ D₁ D₂ f g H).X n))

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- Native P is fixed before the arbitrary derived input is supplied. -/
def inducedDerived (lo hi : ℤ) :
    DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B) := by
  letI : ∀ n, Module.Projective Bᵐᵒᵖ
      (ComplexTensor.rightTerm k B (right k B (InducedRectification.total s D₀ D₁ D₂ f g H)) n) :=
    fun n => induced_term_projective s D₀ D₁ D₂ f g H h₀ h₁ h₂ n
  exact derivedInterval k B (InducedRectification.total s D₀ D₁ D₂ f g H) (lo-2) hi

omit [HasDerivedCategory.{u+1} (ModuleCat.{u} B)] in
/-- The selected interval contains the complete actual native P whenever the source complexes have these bounds. -/
theorem induced_complete (lo hi : ℤ)
    (b₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (b₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (b₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n))
    (n : ℤ) (hn : ∀ i, intervalDegrees (lo-2) hi i ≠ n) :
    IsZero ((InducedRectification.total s D₀ D₁ D₂ f g H).X n) :=
  outside_interval_isZero k B _ (lo-2) hi
    (InducedRectification.total_bounded s D₀ D₁ D₂ f g H lo hi b₀ b₁ b₂) n hn
end LittleFinitistic.BimoduleTotal

end

end OAI
