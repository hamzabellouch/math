import OAI.LinearAlgebra.MatrixMultiplication.Duality.Witness
import OAI.LinearAlgebra.MatrixMultiplication.Duality.HiddenInstances

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionColorLaws DualCompletionLaws CompletionPartitions

theorem law_entropy : finiteEntropy law.mass =
    288 * Real.log 2 + 288 * hiddenRate := by
  have hhidden := DualHiddenRates.laws288_weightedHidden
  rw [DualUniform.UniformLaws.entropy_B _ _ DualUniform.laws288_uniform,
    DualUniform.UniformLaws.entropy_C _ _ DualUniform.laws288_uniform] at hhidden
  have hcoord := DualHiddenRates.laws288_coordinateEntropy
  change CompletionEntropyAlgebra.binaryEntropy state288.rho +
      state288.rho * Real.log (activeCount source) +
      (1 - state288.rho) * Real.log (inactiveCount source) =
      Real.log (Fintype.card Word) at hcoord
  rw [word_card, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hcoord
  unfold CompletionEntropyAlgebra.binaryEntropy at hcoord
  dsimp only [source] at hcoord
  norm_num only [Nat.cast_ofNat] at hcoord
  change finiteEntropy (CompletionTerminationLaw.law
      (Script.tensor BaseTwo.flagged Script.dual) .B .C (laws288 .B) (laws288 .C)
      state288.rho _ _).mass = _
  rw [CompletionTerminationLaw.law_entropy _ .B .C (by intro h; cases h)]
  linarith only [hhidden, hcoord]

theorem total_hidden_entropy : finiteEntropy law.mass - finiteEntropy (law.map x).mass =
    288 * hiddenRate := by rw [law_entropy, x_entropy]; ring

end MatrixMultiplication.DualWitness

end

end OAI
