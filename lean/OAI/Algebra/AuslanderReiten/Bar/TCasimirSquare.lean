import OAI.Algebra.AuslanderReiten.Bar.TCasimirEvaluation
import Mathlib.LinearAlgebra.TensorProduct.Associator

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

def squareEvaluation (s t : S) : (R ⊗[k] R) ⊗[k] (R ⊗[k] R) →ₗ[k]
    (R ⊗[k] R) ⊗[k] (S ⊗[k] S) :=
  (TensorProduct.tensorTensorTensorComm k R S R S).toLinearMap.comp
    (TensorProduct.map (evaluateAtSimple q s) (evaluateAtSimple q t))

theorem twistedCasimir_square_evaluation (H : kˣ) (hq1 : 1 + q ≠ 0) (s t : S) :
    squareEvaluation q s t (twistedCasimir q H ⊗ₜ[k] twistedCasimir q H) =
      ((H : k)^2 • (upper q .f ⊗ₜ[k] upper q .f)) ⊗ₜ[k] (s ⊗ₜ[k] t) := by
  simp only [squareEvaluation, LinearMap.comp_apply, TensorProduct.map_tmul,
    twistedCasimir_evaluation q H hq1, LinearEquiv.coe_coe,
    TensorProduct.tensorTensorTensorComm_tmul]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, pow_two]

def squareDetector : (R ⊗[k] R) ⊗[k] (S ⊗[k] S) →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp
    ((TensorProduct.map (evaluatedDetector q) (evaluatedDetector q)).comp
      (TensorProduct.tensorTensorTensorComm k R S R S).symm.toLinearMap)

theorem twistedCasimir_square_evaluation_ne_zero (H : kˣ) (hq1 : 1 + q ≠ 0) :
    squareEvaluation q (CocycleData.simpleGenerator q) (CocycleData.simpleGenerator q)
      (twistedCasimir q H ⊗ₜ[k] twistedCasimir q H) ≠ 0 := by
  intro hz
  have hh := congrArg (squareDetector q) hz
  rw [twistedCasimir_square_evaluation q H hq1] at hh
  simp [squareDetector, TensorProduct.tensorTensorTensorComm_symm,
    TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.smul_tmul'] at hh

end ArExplicit.T

end

end OAI
