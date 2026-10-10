import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluationCharacters
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluationParameters

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Complex
open scoped BigOperators

theorem periodicGaussian_quadratic (q : ℕ) [NeZero q] (ε : ℝ) :
    periodicGaussian q (quadraticResidueWeight q) (ε : ℂ) =
      ∑' n : ℤ, gaussianWave (gaussParameter q ε) n := by
  unfold periodicGaussian
  apply tsum_congr
  intro n
  rw [quadraticResidueWeight_int]
  unfold gaussianWave gaussParameter
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem periodicGaussian_inverse (q : ℕ) [NeZero q] (ε : ℝ) :
    (∑' n : ℤ, gaussianWave (gaussParameter q ε)⁻¹ n) =
      periodicGaussian 4 (inverseResidueWeight q) (gaussResidual q ε) := by
  unfold periodicGaussian
  apply tsum_congr
  intro n
  rw [inverseResidueWeight_int]
  unfold gaussianWave gaussResidual
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

end Ostmann.QuadraticSieve

end

end OAI
