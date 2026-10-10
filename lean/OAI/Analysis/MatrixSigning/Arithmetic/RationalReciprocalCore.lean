import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticEncodingSize
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeCorrect
import OAI.Analysis.MatrixSigning.Arithmetic.RationalReciprocalSwap

namespace OAI

section

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19
open KS.W03.MachineCombinators KS.W30.BinaryRational

def core : Program 13 := compose swap RationalMagnitudeMachine.program

def canonicalState (q : ℚ) : Fin 13 → List Bool :=
  RationalMagnitudeMachine.state (Computability.encodeNat q.num.natAbs)
    (Computability.encodeNat q.den) (decide (q.num < 0))

theorem core_spec (q : ℚ) :
    RunSpec core (canonicalState q) (canonicalState q⁻¹)
      (310 * (KS.W01.ratLength q + 1) ^ 3) := by
  let x := encodeMagnitude q
  let y : RatBits := ⟨x.negative, x.denominator, x.numerator⟩
  have hsize := KS.W01.rational_parts_size_le_length q
  have hn : x.numerator.length ≤ KS.W01.ratLength q := by
    simpa only [x, encodeMagnitude, encodeNat_length_eq_size] using hsize.1
  have hd : x.denominator.length ≤ KS.W01.ratLength q := by
    simpa only [x, encodeMagnitude, encodeNat_length_eq_size] using hsize.2
  have hyc : CanonicalBits y.numerator := canonicalBits_encodeNat _
  have hyd : CanonicalBits y.denominator := canonicalBits_encodeNat _
  have hs := swap_spec x.numerator x.denominator x.negative
  have hnrm := RationalMagnitudeMachine.normalizes_ratBits y (KS.W01.ratLength q) hyc hyd hd hn
  have hout : normalize y = encodeMagnitude q⁻¹ := inverseRat_canonical q
  rw [hout] at hnrm
  have h := hs.compose hnrm
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (KS.W01.ratLength q + 1)
  have ht : (4 * x.numerator.length + 2 * x.denominator.length + 6) +
      300 * (KS.W01.ratLength q + 1) ^ 3 ≤ 310 * (KS.W01.ratLength q + 1) ^ 3 := by omega
  exact h.mono ht

end KS.W30.RationalReciprocal

end

end OAI
