import OAI.Algebra.AuslanderReiten.Evaluation.TensorBetaEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.T
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] (q : k) (hq : 1+q ≠ 0)

 theorem freePair_evaluation (a b c d : T k q) (s t : Resolution.Simple q) :
    ((Resolution.simpleCoordinateEquiv q hq) (b • s) • a) ⊗ₜ[k]
      ((Resolution.simpleCoordinateEquiv q hq) (d • t) • c) =
    A.barZeroCoordinate q (squareEvaluation q s t ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))) := by
  simp only [squareEvaluation, LinearMap.comp_apply, TensorProduct.map_tmul,
    evaluateAtSimple, LinearMap.id_apply, simpleActionAt_apply, LinearEquiv.coe_coe,
    TensorProduct.tensorTensorTensorComm_tmul]
  change (Resolution.simpleCoordinate q (b • s) • a) ⊗ₜ[k]
    (Resolution.simpleCoordinate q (d • t) • c) = _
  erw [A.barZeroCoordinate_tmul, A.simpleCoordinate_tmul]
  exact TensorProduct.smul_tmul_smul (Resolution.simpleCoordinate q (b • s))
    (Resolution.simpleCoordinate q (d • t)) a c

end ArExplicit.T

end

end OAI
