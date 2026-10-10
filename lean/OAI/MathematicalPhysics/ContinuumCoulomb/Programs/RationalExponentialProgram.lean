import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalTaylorRegisters
import OAI.Computability.QuantumFactoring.BitStackProcedures

namespace OAI

/-! A polynomial-time rational exponential evaluator. Magnitude and
precision bounds are supplied in unary; the rational argument and result
are encoded in binary. Every arithmetic operation is an actual stack
program, including the shared-denominator Taylor recurrence. -/

namespace ContinuumCoulomb.RationalExponentialProgram
open ExactQuantumFactoring.BitStackProgram
open RationalTaylorRegisters

noncomputable def stepProgram : Procedure code code step := by
  let a := Procedure.first intCode
    (prodCode Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode))))
  let s₁ := Procedure.second intCode
    (prodCode Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode))))
  let b := (Procedure.first Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode)))).comp s₁
  let s₂ := (Procedure.second Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode)))).comp s₁
  let j := (Procedure.first Nat.bits (prodCode intCode (prodCode Nat.bits intCode))).comp s₂
  let s₃ := (Procedure.second Nat.bits (prodCode intCode (prodCode Nat.bits intCode))).comp s₂
  let A := (Procedure.first intCode (prodCode Nat.bits intCode)).comp s₃
  let s₄ := (Procedure.second intCode (prodCode Nat.bits intCode)).comp s₃
  let F := (Procedure.first Nat.bits intCode).comp s₄
  let P := (Procedure.second Nat.bits intCode).comp s₄
  let next := Procedure.successor.comp j
  let factor := Procedure.binaryMul.comp (next.pair b)
  let nextA := Procedure.intMul.comp ((Procedure.natToInt.comp factor).pair
    (Procedure.intAdd.comp (A.pair P)))
  let nextF := Procedure.binaryMul.comp (factor.pair F)
  let nextP := Procedure.intMul.comp (a.pair P)
  exact (a.pair (b.pair (next.pair (nextA.pair (nextF.pair nextP))))).congrFun
    (by intro s; rfl)

noncomputable def repeatProgram : Procedure (prodCode unaryCode code) code
    (fun x => (step^[x.1]) x.2) :=
  stepProgram.iterate (64 * (Polynomial.X + 1) ^ 2 + 100) iterate_code_bound

noncomputable def initialProgram : Procedure ratCode code initial := by
  let a := Procedure.ratNum
  let b := Procedure.ratDen
  let zero := Procedure.constant ratCode Nat.bits 0
  let zeroInt := Procedure.constant ratCode intCode (0 : ℤ)
  let one := Procedure.constant ratCode Nat.bits 1
  let oneInt := Procedure.constant ratCode intCode (1 : ℤ)
  exact (a.pair (b.pair (zero.pair (zeroInt.pair (one.pair oneInt))))).congrFun
    (by intro q; rfl)

noncomputable def resultProgram : Procedure code ratCode result := by
  let s₁ := Procedure.second intCode
    (prodCode Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode))))
  let s₂ := (Procedure.second Nat.bits (prodCode Nat.bits (prodCode intCode (prodCode Nat.bits intCode)))).comp s₁
  let s₃ := (Procedure.second Nat.bits (prodCode intCode (prodCode Nat.bits intCode))).comp s₂
  let A := (Procedure.first intCode (prodCode Nat.bits intCode)).comp s₃
  let s₄ := (Procedure.second intCode (prodCode Nat.bits intCode)).comp s₃
  let F := (Procedure.first Nat.bits intCode).comp s₄
  exact (Procedure.makeRat.comp (A.pair F)).congrFun (by intro s; rfl)

noncomputable def partialProgram : Procedure (prodCode unaryCode ratCode) ratCode
    (fun x => RationalExponential.taylorSum x.2 x.1) := by
  let n := Procedure.first unaryCode ratCode
  let q := Procedure.second unaryCode ratCode
  let run := repeatProgram.comp (n.pair (initialProgram.comp q))
  exact (resultProgram.comp run).congrFun (by intro x; exact result_correct x.2 x.1)

noncomputable def orderProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => RationalExponential.order x.1 x.2) := by
  let m := Procedure.first unaryCode unaryCode
  let p := Procedure.second unaryCode unaryCode
  let two := Procedure.constant (prodCode unaryCode unaryCode) unaryCode 2
  let square := Procedure.unaryMul.comp (m.pair m)
  let twiceSquare := Procedure.unaryMul.comp (two.pair square)
  let sum := Procedure.unaryAdd.comp
    ((Procedure.unaryAdd.comp (twiceSquare.pair p)).pair two)
  exact (Procedure.unaryMul.comp (two.pair sum)).congrFun (by
    intro x
    change 2 * (2 * (x.1 * x.1) + x.2 + 2) = RationalExponential.order x.1 x.2
    unfold RationalExponential.order
    ring)

abbrev Input := ℕ × (ℕ × ℚ)

def inputCode : Input → List Bool := prodCode unaryCode (prodCode unaryCode ratCode)

def approximate (x : Input) : ℚ := RationalExponential.approximate x.1 x.2.1 x.2.2

noncomputable def program : Procedure inputCode ratCode approximate := by
  let m := Procedure.first unaryCode (prodCode unaryCode ratCode)
  let tail := Procedure.second unaryCode (prodCode unaryCode ratCode)
  let p := (Procedure.first unaryCode ratCode).comp tail
  let q := (Procedure.second unaryCode ratCode).comp tail
  let order := orderProgram.comp (m.pair p)
  exact (partialProgram.comp (order.pair q)).congrFun (by intro x; rfl)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime inputCode ratCode approximate := program.toTM2

theorem error (x : Input) (hx : |(x.2.2 : ℝ)| ≤ x.1) :
    |Real.exp (x.2.2 : ℝ) - (approximate x : ℝ)| ≤ (2 ^ x.2.1 : ℝ)⁻¹ :=
  RationalExponential.error x.1 x.2.1 x.2.2 hx

end ContinuumCoulomb.RationalExponentialProgram

end OAI
