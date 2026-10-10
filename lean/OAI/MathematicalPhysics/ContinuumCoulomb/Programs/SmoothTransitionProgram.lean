import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalSmoothTransition
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalExponentialProgram
import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import OAI.Computability.QuantumFactoring.BitStackUnary

namespace OAI

/-! Literal polynomial-time rational programs for the smooth transition
and the fixed transverse cutoff. All large parameters are unary and each
Taylor exponent has already been bounded in `RationalSmoothTransition`. -/

namespace ContinuumCoulomb.SmoothTransitionProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × ℚ
def inputCode : Input → List Bool := prodCode unaryCode ratCode

noncomputable opaque clipProgram : Procedure ratCode ratCode RationalSmoothTransition.clip := by
  let q := Procedure.identity ratCode
  let zero := Procedure.constant ratCode ratCode (0:ℚ)
  let one := Procedure.constant ratCode ratCode (1:ℚ)
  let negative := Procedure.intSign.comp Procedure.ratNum
  let large := Procedure.intSign.comp (Procedure.ratNum.comp
    (Procedure.ratSub.comp (one.pair q)))
  exact (Procedure.conditional negative zero (Procedure.conditional large one q)).congrFun (by
    intro q
    simp only [Function.comp_apply,Rat.num_neg,decide_eq_true_eq,id_eq]
    unfold RationalSmoothTransition.clip
    split_ifs with hneg hlarge
    · rw [min_eq_right (le_of_lt (hneg.trans (by norm_num))), max_eq_left hneg.le]
    · rw [min_eq_left (by linarith : (1:ℚ) ≤ q), max_eq_right (by norm_num)]
    · rw [min_eq_right (by linarith : q ≤ 1), max_eq_right (le_of_not_gt hneg)])

noncomputable opaque flatProgram : Procedure inputCode ratCode
    (fun x => RationalSmoothTransition.flat x.1 x.2) := by
  let p := Procedure.first unaryCode ratCode
  let q := Procedure.second unaryCode ratCode
  let next := Procedure.unarySuccessor.comp p
  let nextQ := Procedure.natToRat.comp (Procedure.unaryToBits.comp next)
  let cutoff := Procedure.ratInv.comp nextQ
  let positive := Procedure.intSign.comp (Procedure.ratNum.comp
    (Procedure.ratSub.comp (cutoff.pair q)))
  let exponent := Procedure.ratNeg.comp (Procedure.ratInv.comp q)
  let sample := clipProgram.comp (RationalExponentialProgram.program.comp
    (next.pair (next.pair exponent)))
  let zero := Procedure.constant inputCode ratCode (0:ℚ)
  exact (Procedure.conditional positive sample zero).congrFun (by
    intro x
    simp only [Function.comp_apply,Rat.num_neg,decide_eq_true_eq,id_eq,
      Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one]
    unfold RationalSmoothTransition.flat
    congr 1
    simp only [sub_neg])

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode RationalSmoothTransition.precision :=
  (Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode 1000).pair
    Procedure.unarySuccessor)).congrFun (by intro p; rfl)

noncomputable opaque program : Procedure inputCode ratCode
    (fun x => RationalSmoothTransition.approximate x.1 x.2) := by
  let p := precisionProgram.comp (Procedure.first unaryCode ratCode)
  let q := Procedure.second unaryCode ratCode
  let one := Procedure.constant inputCode ratCode (1:ℚ)
  let complement := Procedure.ratSub.comp (one.pair q)
  let left := flatProgram.comp (p.pair q)
  let right := flatProgram.comp (p.pair complement)
  exact (Procedure.ratDiv.comp (left.pair (Procedure.ratAdd.comp (left.pair right)))).congrFun
    (by intro x; rfl)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime inputCode ratCode
      (fun x => RationalSmoothTransition.approximate x.1 x.2) := program.toTM2

def cutoffArgument (q : ℚ) : ℚ := (4-q^2)/3
def cutoff (p : ℕ) (q : ℚ) : ℚ :=
  RationalSmoothTransition.approximate p (cutoffArgument q)

noncomputable opaque cutoffArgumentProgram : Procedure ratCode ratCode cutoffArgument := by
  let q := Procedure.identity ratCode
  let four := Procedure.constant ratCode ratCode (4:ℚ)
  let three := Procedure.constant ratCode ratCode (3:ℚ)
  let square := Procedure.ratMul.comp (q.pair q)
  exact (Procedure.ratDiv.comp ((Procedure.ratSub.comp (four.pair square)).pair three)).congrFun
    (by intro q; simp only [cutoffArgument,pow_two]; rfl)

noncomputable opaque cutoffProgram : Procedure inputCode ratCode (fun x => cutoff x.1 x.2) :=
  (program.comp ((Procedure.first unaryCode ratCode).pair
    (cutoffArgumentProgram.comp (Procedure.second unaryCode ratCode)))).congrFun (by intro x; rfl)

noncomputable def cutoffCertificate : Turing.TM2ComputableInPolyTime inputCode ratCode
    (fun x => cutoff x.1 x.2) := cutoffProgram.toTM2

end ContinuumCoulomb.SmoothTransitionProgram

end OAI
