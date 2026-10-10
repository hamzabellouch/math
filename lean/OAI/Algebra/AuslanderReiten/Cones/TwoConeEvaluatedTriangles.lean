import OAI.Algebra.AuslanderReiten.Cones.TwoConeBoundaryIdentification
import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleEvaluation
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingProducts
import OAI.Algebra.AuslanderReiten.Cones.TwoTriangleFiltration

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.TwoCone
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (X : FiniteLeftModule k R) (τ : FrobeniusTrace k R)

omit [Module.Finite k R] in
include hr in
private theorem middle_right_projective (n : ℕ) : Module.Projective Rᵐᵒᵖ
    (EnvelopingBimodule k R (middleCokernelModule D hf n).carrier) := by
  let := hr (n + 2)
  exact EnvelopingBimodule.prod_right_projective
    (baseCokernelModule D hf (n + 2)).carrier (baseCokernelModule D hf (n + 2)).carrier

def evaluatedSkeletonTriangle (n : ℕ) :
    Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  letI := middle_right_projective D hf hr n
  exact FiniteLeftModule.evaluationTriangle X
    (M := baseCokernelModule D hf n) (N := skeletonCokernelModule D hf n)
    (P := middleCokernelModule D hf n)
    (bottomCokernelInclusion D n) (singletonCokernelProjection D n)
    (bottomCokernelInclusion_injective D hex n) (singletonCokernelProjection_surjective D n)
    (skeletonCokernel_exact D n) τ

theorem evaluatedSkeletonTriangle_distinguished (n : ℕ) :
    evaluatedSkeletonTriangle D hf hex hr X τ n ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let := middle_right_projective D hf hr n
  exact FiniteLeftModule.evaluationTriangle_distinguished _ _ _ _ _ _ _

def evaluatedTopTriangle (n : ℕ) :
    Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  letI := hr (n + 4)
  exact FiniteLeftModule.evaluationTriangle X
    (M := skeletonCokernelModule D hf n) (N := cokernelModule D hf n)
    (P := baseCokernelModule D hf (n + 4))
    (skeletonCokernelInclusion D n) (topCokernelProjection D n)
    (skeletonCokernelInclusion_injective D hex n) (topCokernelProjection_surjective D n)
    (topCokernel_exact D n) τ

theorem evaluatedTopTriangle_distinguished (n : ℕ) :
    evaluatedTopTriangle D hf hex hr X τ n ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let := hr (n + 4)
  exact FiniteLeftModule.evaluationTriangle_distinguished _ _ _ _ _ _ _

def evaluatedHomFiltration (V : HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (n : ℕ) :=
  twoTriangleHomFiltration k V
    (evaluatedSkeletonTriangle D hf hex hr X τ n).mor₁
    (evaluatedSkeletonTriangle D hf hex hr X τ n).mor₂
    (evaluatedSkeletonTriangle D hf hex hr X τ n).mor₃
    (evaluatedTopTriangle D hf hex hr X τ n).mor₁
    (evaluatedTopTriangle D hf hex hr X τ n).mor₂
    (evaluatedTopTriangle D hf hex hr X τ n).mor₃
    (evaluatedSkeletonTriangle_distinguished D hf hex hr X τ n)
    (evaluatedTopTriangle_distinguished D hf hex hr X τ n)

end ArExplicit.TwoCone

end

end OAI
