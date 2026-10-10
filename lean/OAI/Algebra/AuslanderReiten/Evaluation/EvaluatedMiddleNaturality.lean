import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedMiddleShift

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (X : FiniteLeftModule k R) (τ : FrobeniusTrace k R)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)

def middleProjection (first : Bool) (n : ℕ) :
    (middleCokernelModule D hf n).carrier →ₗ[R ⊗[k] Rᵐᵒᵖ]
      (baseCokernelModule D hf (n+2)).carrier :=
  if first then LinearMap.fst _ _ _ else LinearMap.snd _ _ _

def middleTermProjection (first : Bool) (n : ℕ) :
    (middleTermModule D hf n).carrier →ₗ[R ⊗[k] Rᵐᵒᵖ]
      (termModule D hf (n+2)).carrier :=
  if first then LinearMap.fst _ _ _ else LinearMap.snd _ _ _

omit [Module.Finite k R] in
theorem middleProjection_cover (first : Bool) (n : ℕ) :
    (middleTermProjection D hf first n).comp (middleStepInclusion D hex n) =
      (baseStepInclusion D hex (n+2)).comp (middleProjection D hf first (n+1)) := by
  cases first <;> rfl

omit [Module.Finite k R] in
theorem middleProjection_quotient (first : Bool) (n : ℕ) :
    ((LinearMap.range (D.d (n+2))).mkQ).comp (middleTermProjection D hf first n) =
      (middleProjection D hf first n).comp (middleCoverQuotient D n) := by
  cases first <;> rfl

theorem evaluatedMiddleProjection_step (first : Bool) (n : ℕ) :
    (Q).map (FiniteLeftModule.resolutionMap τ
      (FiniteLeftModule.evaluationMap X (middleProjection D hf first n))) ≫
        (evaluatedBaseSuccessorIso D hf hex hr hp X τ (n+2)).hom =
    (evaluatedMiddleSuccessorIso D hf hex hr hp X τ n).hom ≫
      (CategoryTheory.shiftFunctor HC (1 : ℤ)).map
        ((Q).map (FiniteLeftModule.resolutionMap τ
          (FiniteLeftModule.evaluationMap X (middleProjection D hf first (n+1))))) := by
  let := hr (n+2)
  let : Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R
      (middleCokernelModule D hf n).carrier) :=
    EnvelopingBimodule.prod_right_projective
      (baseCokernelModule D hf (n+2)).carrier (baseCokernelModule D hf (n+2)).carrier
  let := hp (n+2)
  have h := FiniteLeftModule.evaluationConnecting_natural X τ
    (M₁ := middleCokernelModule D hf (n+1)) (N₁ := middleTermModule D hf n)
    (P₁ := middleCokernelModule D hf n)
    (M₂ := baseCokernelModule D hf (n+3)) (N₂ := termModule D hf (n+2))
    (P₂ := baseCokernelModule D hf (n+2))
    (middleStepInclusion D hex n) (middleCoverQuotient D n)
    (baseStepInclusion D hex (n+2)) (LinearMap.range (D.d (n+2))).mkQ
    (middleStepInclusion_injective D hex n) (middleCoverQuotient_surjective D n)
    (middleStep_exact D hex n)
    (baseStepInclusion_injective D hex (n+2)) (Submodule.mkQ_surjective _) (baseStep_exact D hex (n+2))
    (middleProjection D hf first (n+1)) (middleTermProjection D hf first n)
    (middleProjection D hf first n)
    (middleProjection_cover D hf hex first n) (middleProjection_quotient D hf first n)
  dsimp only [evaluatedBaseSuccessorIso, evaluatedMiddleSuccessorIso]
  erw [FiniteLeftModule.evaluationSuccessorIso_hom,
    FiniteLeftModule.evaluationSuccessorIso_hom]
  exact h

end ArExplicit.TwoCone

end

end OAI
