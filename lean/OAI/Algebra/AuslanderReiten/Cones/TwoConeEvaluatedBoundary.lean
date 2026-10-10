import OAI.Algebra.AuslanderReiten.Cones.TwoConeEvaluatedTriangles

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.TwoCone
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (X : FiniteLeftModule k R) (τ : FrobeniusTrace k R)

include hr in
omit [Module.Finite k R] in
private theorem middle_right (n : ℕ) : Module.Projective Rᵐᵒᵖ
    (EnvelopingBimodule k R (middleCokernelModule D hf n).carrier) := by
  let := hr (n + 2)
  exact EnvelopingBimodule.prod_right_projective
    (baseCokernelModule D hf (n + 2)).carrier (baseCokernelModule D hf (n + 2)).carrier

def evaluatedMiddleSuccessorIso (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj
      ((X.evaluated (middleCokernelModule D hf n)).completeCochain τ) ≅
    ((HomotopyCategory.quotient _ _).obj
      ((X.evaluated (middleCokernelModule D hf (n + 1))).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI := middle_right D hf hr n
  letI := hp (n + 2)
  exact FiniteLeftModule.evaluationSuccessorIso X
    (M := middleCokernelModule D hf (n + 1)) (N := middleTermModule D hf n)
    (P := middleCokernelModule D hf n)
    (middleStepInclusion D hex n) (middleCoverQuotient D n)
    (middleStepInclusion_injective D hex n) (middleCoverQuotient_surjective D n)
    (middleStep_exact D hex n) τ

def evaluatedBaseSuccessorIso (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj
      ((X.evaluated (baseCokernelModule D hf n)).completeCochain τ) ≅
    ((HomotopyCategory.quotient _ _).obj
      ((X.evaluated (baseCokernelModule D hf (n + 1))).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI := hr n
  letI := hp n
  exact FiniteLeftModule.evaluationSuccessorIso X
    (M := baseCokernelModule D hf (n + 1)) (N := termModule D hf n)
    (P := baseCokernelModule D hf n)
    (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ
    (baseStepInclusion_injective D hex n) (Submodule.mkQ_surjective _)
    (baseStep_exact D hex n) τ

theorem evaluatedSkeletonConnecting_eq (n : ℕ) :
    (evaluatedSkeletonTriangle D hf hex hr X τ n).mor₃ =
      (evaluatedMiddleSuccessorIso D hf hex hr hp X τ n).hom ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
          ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
            (FiniteLeftModule.evaluationMap X
              (M := middleCokernelModule D hf (n + 1)) (N := baseCokernelModule D hf n)
              (rowCokernelMap D n)))) := by
  let := middle_right D hf hr n
  let := hp (n + 2)
  have h := FiniteLeftModule.evaluationConnecting_natural X τ
    (M₁ := middleCokernelModule D hf (n + 1)) (N₁ := middleTermModule D hf n)
    (P₁ := middleCokernelModule D hf n)
    (M₂ := baseCokernelModule D hf n) (N₂ := skeletonCokernelModule D hf n)
    (P₂ := middleCokernelModule D hf n)
    (middleStepInclusion D hex n) (middleCoverQuotient D n)
    (bottomCokernelInclusion D n) (singletonCokernelProjection D n)
    (middleStepInclusion_injective D hex n) (middleCoverQuotient_surjective D n) (middleStep_exact D hex n)
    (bottomCokernelInclusion_injective D hex n) (singletonCokernelProjection_surjective D n)
    (skeletonCokernel_exact D n)
    (rowCokernelMap D n) (singletonCoverLift D n) LinearMap.id
    (singletonCoverLift_boundary D hex n)
    (by simpa only [LinearMap.id_comp, middleCoverQuotient] using singletonCoverLift_projection D n)
  erw [FiniteLeftModule.evaluationMap_id,
    FiniteLeftModule.resolutionMap_id τ (M := X.evaluated (middleCokernelModule D hf n)),
    Category.id_comp] at h
  dsimp only [evaluatedSkeletonTriangle, evaluatedMiddleSuccessorIso]
  erw [FiniteLeftModule.evaluationSuccessorIso_hom]
  exact h

theorem evaluatedTopConnecting_eq (n : ℕ) :
    (evaluatedTopTriangle D hf hex hr X τ n).mor₃ =
      (evaluatedBaseSuccessorIso D hf hex hr hp X τ (n + 4)).hom ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
          ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
            (FiniteLeftModule.evaluationMap X
              (M := baseCokernelModule D hf (n + 5)) (N := skeletonCokernelModule D hf n)
              (-(topAttachingCokernel D n))))) := by
  let := hr (n + 4)
  let := hp (n + 4)
  have h := FiniteLeftModule.evaluationConnecting_natural X τ
    (M₁ := baseCokernelModule D hf (n + 5)) (N₁ := termModule D hf (n + 4))
    (P₁ := baseCokernelModule D hf (n + 4))
    (M₂ := skeletonCokernelModule D hf n) (N₂ := cokernelModule D hf n)
    (P₂ := baseCokernelModule D hf (n + 4))
    (baseStepInclusion D hex (n + 4)) (LinearMap.range (D.d (n + 4))).mkQ
    (skeletonCokernelInclusion D n) (topCokernelProjection D n)
    (baseStepInclusion_injective D hex (n + 4)) (Submodule.mkQ_surjective _) (baseStep_exact D hex (n + 4))
    (skeletonCokernelInclusion_injective D hex n) (topCokernelProjection_surjective D n)
    (topCokernel_exact D n)
    (-(topAttachingCokernel D n)) (topCoverLift D n) LinearMap.id
    (topCoverLift_boundary D hex n)
    (by simpa only [LinearMap.id_comp] using topCoverLift_projection D n)
  erw [FiniteLeftModule.evaluationMap_id,
    FiniteLeftModule.resolutionMap_id τ (M := X.evaluated (baseCokernelModule D hf (n + 4))),
    Category.id_comp] at h
  dsimp only [evaluatedTopTriangle, evaluatedBaseSuccessorIso]
  erw [FiniteLeftModule.evaluationSuccessorIso_hom]
  exact h

end ArExplicit.TwoCone

end

end OAI
