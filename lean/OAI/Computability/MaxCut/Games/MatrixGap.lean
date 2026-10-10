import Mathlib
import OAI.Computability.MaxCut.Games.ProductSoundness
import OAI.Computability.MaxCut.Encoding.BinaryParityReduction
import OAI.Computability.MaxCut.Machines.AddressMachineLoop

namespace OAI

namespace MaxCutGames.FromMatrixGap

open MaxCutGames.Foundations Target
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Integration
open MaxCutGames.Reduction
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
end MaxCutGames.FromMatrixGap

/-!
# Size of a binary row kernel

An `r`-row linear constraint on `ℓ` binary coordinates leaves a kernel with at
least `2^(ℓ-r)` elements.  This does not require independent constraint rows.
The exponent uses natural subtraction, so the assertion also covers `r > ℓ`.
The argument is rank--nullity followed by the exact finite-field cardinality
formula; it does not use any inverse theorem or rank-level inequality.
-/

namespace MaxCutGames.Inverse

/-- Even dependent binary row constraints remove at most one dimension per
row. -/
theorem binary_kernel_finrank_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    ℓ - r ≤ Module.finrank (ZMod 2) A.ker := by
  have hnull : Module.finrank (ZMod 2) A.range +
      Module.finrank (ZMod 2) A.ker = ℓ := by
    simpa only [Module.finrank_fin_fun] using A.finrank_range_add_finrank_ker
  have hrange : Module.finrank (ZMod 2) A.range ≤ r := by
    simpa only [Module.finrank_fin_fun] using A.range.finrank_le
  apply Nat.sub_le_iff_le_add.mpr
  calc
    ℓ = Module.finrank (ZMod 2) A.ker +
        Module.finrank (ZMod 2) A.range := hnull.symm.trans (Nat.add_comm _ _)
    _ ≤ Module.finrank (ZMod 2) A.ker + r :=
      Nat.add_le_add_left hrange _

/-- The cardinality of the binary row kernel is at least `2^(ℓ-r)`. -/
theorem binary_kernel_card_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    2 ^ (ℓ - r) ≤ Nat.card A.ker := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) (binary_kernel_finrank_lower A)

end MaxCutGames.Inverse

end OAI
