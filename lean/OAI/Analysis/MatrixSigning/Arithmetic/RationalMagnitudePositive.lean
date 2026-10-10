import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeDivision
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeSign

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19 KS.W30.BinaryGCD

theorem positive_output_pair (n d : List Bool) (hd : 0 < bitsValue d) :
    let g := Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d))
    KS.W30.BinaryRational.normalizeMagnitude n d =
      (trimBits (DivisionLoop.process g n.reverse [] []).1,
       trimBits (DivisionLoop.process g d.reverse [] []).1) := by
  dsimp only
  have hg : 0 < bitsValue (Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d))) := by
    rw [bitsValue_encodeNat]
    exact Nat.gcd_pos_of_pos_right _ hd
  have hd' : trimBits d ≠ [] := by
    intro h
    have hh := (trim_eq_nil_iff d).mp h
    omega
  rw [KS.W30.BinaryRational.normalizeMagnitude, ite_eq_right hd', gcdBits_eq_encodeNat,
    KS.W30.BinaryRational.divisionLoop_trim_quotient _ n hg,
    KS.W30.BinaryRational.divisionLoop_trim_quotient _ d hg]

theorem positiveBranch_spec (n d : List Bool) (sgn : Bool) (L : ℕ)
    (hnc : CanonicalBits n) (hdc : CanonicalBits d)
    (hn : n.length ≤ L) (hd : d.length ≤ L) (hdp : 0 < bitsValue d) :
    let p := KS.W30.BinaryRational.normalizeMagnitude n d
    RunSpec positiveBranch (state n d sgn)
      (state p.1 p.2 (if p.1 = [] then false else sgn)) (250 * (L + 1) ^ 3) := by
  dsimp only
  let g := Computability.encodeNat (Nat.gcd (bitsValue n) (bitsValue d))
  let qn := DivisionLoop.process g n.reverse [] []
  let qd := DivisionLoop.process g d.reverse [] []
  have hg : g.length ≤ L := GCDMachine.gcd_encode_length_le n d L hn hd
  have hsetup := computeGCD_spec n d sgn L hnc hdc hn hd
  have hnrun := reduceNumerator_spec g n d sgn L hg hn
  have hdrun := reduceDenominator_spec g (trimBits qn.1) d sgn L hg hd
  have hfinish := (clearGCD_spec g (trimBits qn.1) (trimBits qd.1) sgn).compose
    (normalizeSign_spec (trimBits qn.1) (trimBits qd.1) sgn)
  have h := hsetup.compose (hnrun.compose (hdrun.compose hfinish))
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (L + 1)
  have hquad : (L + 1) ^ 2 ≤ (L + 1) ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have ht : 120 * (L + 1) ^ 3 + (50 * (L + 1) ^ 2 +
      (50 * (L + 1) ^ 2 + ((g.length + 1) + 2))) ≤ 250 * (L + 1) ^ 3 := by omega
  have hp : KS.W30.BinaryRational.normalizeMagnitude n d =
      (trimBits qn.1, trimBits qd.1) := positive_output_pair n d hdp
  simpa only [positiveBranch, hp] using h.mono ht

end KS.W30.RationalMagnitudeMachine

end

end OAI
