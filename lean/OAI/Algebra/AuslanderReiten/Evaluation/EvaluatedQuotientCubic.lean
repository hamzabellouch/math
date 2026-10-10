import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedBaseQuotient
import OAI.Algebra.AuslanderReiten.Homology.LinearCokernelMap

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
variable (X : FiniteLeftModule k R)

def evaluatedFirstBaseMap (n : ℕ) :
    evaluatedRawTerm D hf X (n+3) →ₗ[R] evaluatedRawTerm D hf X n :=
  FiniteLeftModule.evaluationMap X (D.first n)

def evaluatedSecondBaseMap (n : ℕ) :
    evaluatedRawTerm D hf X (n+3) →ₗ[R] evaluatedRawTerm D hf X n :=
  FiniteLeftModule.evaluationMap X (D.second n)

omit [Module.Finite k R] in
theorem evaluatedFirstBaseMap_comm (n : ℕ) :
    (evaluatedFirstBaseMap D hf X n).comp (evaluatedBaseDifferential D hf X (n+3)) =
      (evaluatedBaseDifferential D hf X n).comp (evaluatedFirstBaseMap D hf X (n+1)) := by
  dsimp only [evaluatedFirstBaseMap, evaluatedBaseDifferential]
  rw [← FiniteLeftModule.evaluationMap_comp, ← FiniteLeftModule.evaluationMap_comp,
    D.first_comm]

omit [Module.Finite k R] in
theorem evaluatedSecondBaseMap_comm (n : ℕ) :
    (evaluatedSecondBaseMap D hf X n).comp (evaluatedBaseDifferential D hf X (n+3)) =
      (evaluatedBaseDifferential D hf X n).comp (evaluatedSecondBaseMap D hf X (n+1)) := by
  dsimp only [evaluatedSecondBaseMap, evaluatedBaseDifferential]
  rw [← FiniteLeftModule.evaluationMap_comp, ← FiniteLeftModule.evaluationMap_comp,
    D.second_comm]

omit [Module.Finite k R] in
theorem evaluatedFirstBaseMap_quotient (n : ℕ) :
    (evaluatedBaseQuotient D hf X n).comp (evaluatedFirstBaseMap D hf X n) =
      (FiniteLeftModule.evaluationMap X
        (M := baseCokernelModule D hf (n+3)) (N := baseCokernelModule D hf n)
        (firstCokernelMap D n)).comp (evaluatedBaseQuotient D hf X (n+3)) := by
  dsimp only [evaluatedBaseQuotient, evaluatedFirstBaseMap]
  rw [← FiniteLeftModule.evaluationMap_comp, ← FiniteLeftModule.evaluationMap_comp,
    firstCokernelMap_quotient D n]

omit [Module.Finite k R] in
theorem evaluatedSecondBaseMap_quotient (n : ℕ) :
    (evaluatedBaseQuotient D hf X n).comp (evaluatedSecondBaseMap D hf X n) =
      (FiniteLeftModule.evaluationMap X
        (M := baseCokernelModule D hf (n+3)) (N := baseCokernelModule D hf n)
        (secondCokernelMap D n)).comp (evaluatedBaseQuotient D hf X (n+3)) := by
  dsimp only [evaluatedBaseQuotient, evaluatedSecondBaseMap]
  rw [← FiniteLeftModule.evaluationMap_comp, ← FiniteLeftModule.evaluationMap_comp,
    secondCokernelMap_quotient D n]

def evaluatedFirstRawCokernel (n : ℕ) :=
  LinearCokernel.map (evaluatedBaseDifferential D hf X (n+3))
    (evaluatedBaseDifferential D hf X n) (evaluatedFirstBaseMap D hf X (n+1))
    (evaluatedFirstBaseMap D hf X n) (evaluatedFirstBaseMap_comm D hf X n)

def evaluatedSecondRawCokernel (n : ℕ) :=
  LinearCokernel.map (evaluatedBaseDifferential D hf X (n+3))
    (evaluatedBaseDifferential D hf X n) (evaluatedSecondBaseMap D hf X (n+1))
    (evaluatedSecondBaseMap D hf X n) (evaluatedSecondBaseMap_comm D hf X n)

omit [Module.Finite k R] in
theorem evaluatedBaseCokernelEquiv_first (n : ℕ)
    (z : evaluatedRawTerm D hf X (n+3) ⧸ LinearMap.range (evaluatedBaseDifferential D hf X (n+3))) :
    evaluatedBaseCokernelEquiv D hf hex hr X n (evaluatedFirstRawCokernel D hf X n z) =
      FiniteLeftModule.evaluationMap X
        (M := baseCokernelModule D hf (n+3)) (N := baseCokernelModule D hf n)
        (firstCokernelMap D n) (evaluatedBaseCokernelEquiv D hf hex hr X (n+3) z) := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (evaluatedBaseDifferential D hf X (n+3))).mkQ_surjective z
  change evaluatedBaseQuotient D hf X n (evaluatedFirstBaseMap D hf X n z) = _
  exact DFunLike.congr_fun (evaluatedFirstBaseMap_quotient D hf X n) z

omit [Module.Finite k R] in
theorem evaluatedBaseCokernelEquiv_second (n : ℕ)
    (z : evaluatedRawTerm D hf X (n+3) ⧸ LinearMap.range (evaluatedBaseDifferential D hf X (n+3))) :
    evaluatedBaseCokernelEquiv D hf hex hr X n (evaluatedSecondRawCokernel D hf X n z) =
      FiniteLeftModule.evaluationMap X
        (M := baseCokernelModule D hf (n+3)) (N := baseCokernelModule D hf n)
        (secondCokernelMap D n) (evaluatedBaseCokernelEquiv D hf hex hr X (n+3) z) := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (evaluatedBaseDifferential D hf X (n+3))).mkQ_surjective z
  change evaluatedBaseQuotient D hf X n (evaluatedSecondBaseMap D hf X n z) = _
  exact DFunLike.congr_fun (evaluatedSecondBaseMap_quotient D hf X n) z

end ArExplicit.TwoCone

end

end OAI
