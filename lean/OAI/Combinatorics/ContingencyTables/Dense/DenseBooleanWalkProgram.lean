import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseWalkSemantics

namespace OAI

/-! # A polynomial program for the complete flat-word dense walk -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary ProfilePrograms

def denseWidthRealizer : Realizer denseStepBits := by
  let index := composition (composition (pair (constant 8) identity) multiply) ceilLogTwoRealizer
  let coins := composition (pair (constant 8) fifthPower) multiply
  exact composition (pair index coins) add

theorem polynomial_denseWidth : PolynomialTime denseWidthRealizer := by
  unfold denseWidthRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_pair (polynomial_constant 8) polynomial_identity) polynomial_multiply)
      polynomial_ceilLogTwo)
    (polynomial_composition (polynomial_pair (polynomial_constant 8) polynomial_fifthPower)
      polynomial_multiply)) polynomial_add

def flatWordWalk (z : FlatExponentData×List Bool) : FlatExponentData :=
  walkWords (z.1,wordChunks (denseStepBits z.1.2,z.2))

def flatWordWalkRealizer : Realizer flatWordWalk :=
  composition (pair first (composition (pair
    (composition (composition first second) denseWidthRealizer) second) wordChunksRealizer))
    walkWordsRealizer

theorem polynomial_flatWordWalk : PolynomialTime flatWordWalkRealizer :=
  polynomial_composition (polynomial_pair polynomial_first (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_denseWidth)
    polynomial_second) polynomial_wordChunks)) polynomial_walkWords

lemma denseStepBits_pos {d : ℕ} (hd : 0<d) : 0<denseStepBits d := by
  have h := Nat.mul_pos (by decide : 0<8) (pow_pos hd 5)
  exact h.trans_le (Nat.le_add_left _ _)

noncomputable section
open scoped Classical

/-- The literal flat-bit program computes exactly the finite Boolean walk.
The polynomial runtime theorem above applies to every input word. -/
theorem flatWordWalk_code {m n d : ℕ} (hd : 0<d)
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (steps : ℕ)
    (bits : Fin (steps*denseStepBits d) → Bool) :
    flatWordWalk ((((marginCode R,marginCode P),gridNatCode a),d),List.ofFn bits)=
      (((marginCode R,marginCode P),
        gridNatCode (denseBooleanWalk R P d finProdFinEquiv a steps bits)),d) := by
  dsimp only [flatWordWalk]
  rw [wordChunks_ofFn (denseStepBits_pos hd) bits]
  exact walkWords_ofFn R P a steps (gridWordEquiv steps (denseStepBits d) bits)

end
end ContingencyTables.DensePrograms

end OAI
