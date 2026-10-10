import OAI.Algebra.Finitistic.Bimodule.BoundedBimoduleDerived
import OAI.Algebra.Finitistic.Bimodule.BimoduleScalarEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- Build the complete derived-tensor model from the actual native rectification, with no tensor-comparison assumption. -/
def inducedBoundedProjective
    {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
    (s : Quadratic k B (A := A) (J := J) (R := R))
    (D₀ D₁ D₂ : RightComplex B) (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
    (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)
    (lo hi : ℤ)
    (b₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (b₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (b₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n))
    (h₀ : ∀ n, Module.Projective Bᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Projective Bᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Projective Bᵐᵒᵖ (D₂.X n)) :
    BoundedProjective k B (InducedRectification.total s D₀ D₁ D₂ f g H) where
  lower := lo-2
  upper := hi
  bounded := InducedRectification.total_bounded s D₀ D₁ D₂ f g H lo hi b₀ b₁ b₂
  projective := induced_term_projective s D₀ D₁ D₂ f g H h₀ h₁ h₂

namespace BoundedProjective
variable {P : BiComplex k B} (data : BoundedProjective k B P)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- The exact native module-valued degree-zero evaluation, using the module's original compatible k action. -/
def nativeEvaluation (N : Type u) [AddCommGroup N] [Module k N] [Module B N] [IsScalarTower k B N] :
    data.derived.obj (DerivedCategory.Q.obj (singleInput B (ModuleCat.of B N))) ≅
      DerivedCategory.Q.obj (((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P) :=
  data.singleEvaluation (ModuleCat.of B N) ≪≫ DerivedCategory.Q.mapIso (scalarEvaluationIso k B N P)
end BoundedProjective
end LittleFinitistic.BimoduleTotal

end

end OAI
