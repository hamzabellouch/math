import OAI.Computability.UniqueGames.Decoding.ActualSeedSamplingLemmas
import OAI.Computability.UniqueGames.Machines.MachineSingleOrbitBridgeLemmas
import OAI.Computability.UniqueGames.PCP.BinaryParityReduction
import OAI.Computability.UniqueGames.Reduction.FinishReduction

namespace OAI


namespace UniqueGamesTheorem.FromMatrixGap


open UniqueGamesTheorem.Foundations Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Integration
open UniqueGamesTheorem.Reduction
open Explicit

noncomputable section

/-- Choose the parity error only after the matrix tuple length is fixed, then
compose the actual raw-input, matrix-test, and final graph machines. -/
def reduction {ε δ : ℝ} (P : ParameterSelection.OuterParameters ε δ)
    (M : Decoder.MatrixGap.Parameters P.pStar) :
    MachineOutputContract.BinaryGapReduction ε δ := by
  classical
  have hk : 0 < M.k := M.k_pos
  let ξ := Classical.choose (P.exists_parity_error M.k hk)
  have hξspec := Classical.choose_spec (P.exists_parity_error M.k hk)
  have hξ : 0 < ξ := hξspec.1
  have hξsmall : ξ < 1 / 100 := hξspec.2.1
  have hξbudget : ξ < P.epsilon0 / (2 * M.k * P.repetitions) := hξspec.2.2
  let R := Classical.choice (Outer.BinaryParityReduction.exists_reduction ξ hξ hξsmall)
  let matrix := fun input => MachineSingleOrbitBridge.output M.k M.T (R.reduce input)
  let matrixMachine := MachineSequential.composeBits
    (f := R.reduce) (g := MachineSingleOrbitBridge.output M.k M.T)
    R.computation (MachineSingleOrbitBridge.computableInPolyTime M.k M.T)
  have matrixFinite : MachineFiniteAlphabet.FiniteAlphabet matrixMachine.tm :=
    MachineFiniteAlphabet.composeBits
      (f := R.reduce) (g := MachineSingleOrbitBridge.output M.k M.T)
      R.computation (MachineSingleOrbitBridge.computableInPolyTime M.k M.T)
      R.finiteAlphabet (MachineSingleOrbitBridge.workAlphabetFinite M.k M.T)
  have hq : 2 ≤ 2 ^ M.s := Nat.le_self_pow (by have h := M.s_pos; omega) 2
  refine FinishReduction.of_matrix_reduction P hq M.s_pos
    (Encoding.alphabetEquiv M.s).symm matrix ?_ matrixMachine matrixFinite
    ((M.k : ℚ) * ξ + P.pStar / 2)
    (P.matrix_error_budget M.k hk ξ hξbudget.le) ?_ ?_
  · intro input
    exact M.output_translations (Outer.HastadSource.asSource (R.reduce input))
  · intro input yes
    obtain ⟨assignment, hfailure⟩ :=
      Outer.BinaryParityReduction.failure_completeness R input yes
    have h := M.completeness (Outer.HastadSource.asSource (R.reduce input))
      assignment ξ hfailure
    simpa only [matrix, MachineSingleOrbitBridge.output,
      MachineSingleOrbitBridge.SingleAddress.tableOutput, Outer.HastadSource.asSource,
      Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat] using h
  · intro input no
    exact M.sound (Outer.HastadSource.asSource (R.reduce input))
      (R.distinct input) (Outer.BinaryParityReduction.parity_soundness R input no)

end
end UniqueGamesTheorem.FromMatrixGap

end OAI
