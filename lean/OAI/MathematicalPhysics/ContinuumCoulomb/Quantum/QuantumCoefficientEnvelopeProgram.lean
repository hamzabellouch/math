import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawEnvelope
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedFinalBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeEnvelope

namespace OAI

/-! Literal unary programs for the logical and physical coefficient bounds.
The only arguments are qubit count, term count, initial magnitude and precision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientEnvelopeProgram
open ExactQuantumFactoring.BitStackProgram

private noncomputable def add {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x+g x) := Procedure.unaryAdd.comp (p.pair q)
private noncomputable def mul {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x*g x) := Procedure.unaryMul.comp (p.pair q)
private noncomputable def constant {α : Type} (ea : α → List Bool) (n : ℕ) :
    Procedure ea unaryCode (fun _ => n) := Procedure.constant ea unaryCode n
private noncomputable def square {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^2) :=
  (mul p p).congrFun (by intro x; exact (pow_two _).symm)
private noncomputable def cube {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^3) :=
  (mul (square p) p).congrFun (by intro x; exact (pow_succ _ 2).symm)
private noncomputable def fourth {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^4) :=
  (square (square p)).congrFun (by intro x; simp only [← pow_mul])

noncomputable opaque weightProgram {α : Type} {ea : α → List Bool} {R B : α → ℕ}
    (pr : Procedure ea unaryCode R) (pb : Procedure ea unaryCode B) :
    Procedure ea unaryCode (fun x => QuantumOrderedXZ.weightNat (R x) (B x)) := by
  let c := constant ea
  exact (add (add (add (add (add (cube pr) (mul (square pr) pb)) (square pr))
    (mul pr (add (c 1) (square pb)))) (c 1)) (square pb)).congrFun (by intro x; rfl)

noncomputable opaque logicalScaleProgram {α : Type} {ea : α → List Bool} {m B N : α → ℕ}
    (pm : Procedure ea unaryCode m) (pb : Procedure ea unaryCode B)
    (pn : Procedure ea unaryCode N) :
    Procedure ea unaryCode (fun x => QuantumOrderedXZ.scaleNat (m x) (B x) (N x)) := by
  let c := constant ea
  exact (mul (mul (c 8) (fourth (mul (c 4) (add (c 1)
    (mul pm (square (add (c 1) pb))))))) pn).congrFun (by intro x; rfl)

noncomputable opaque stepProgram {α : Type} {ea : α → List Bool} {m B N : α → ℕ}
    (pm : Procedure ea unaryCode m) (pb : Procedure ea unaryCode B)
    (pn : Procedure ea unaryCode N) :
    Procedure ea unaryCode (fun x => QuantumOrderedXZ.stepNat (m x) (B x) (N x)) :=
  weightProgram (logicalScaleProgram pm pb pn) pb

noncomputable def logicalProgram {α : Type} {ea : α → List Bool} {m B N : α → ℕ}
    (pm : Procedure ea unaryCode m) (pb : Procedure ea unaryCode B)
    (pn : Procedure ea unaryCode N) (k : ℕ) :
    Procedure ea unaryCode (fun x => QuantumOrderedXZ.pipelineNat (m x) (B x) (N x) k) := by
  induction k with
  | zero => exact pb
  | succ k ih => exact stepProgram (mul (constant ea 3136) pm) ih pn

noncomputable opaque rawBudgetProgram {α : Type} {ea : α → List Bool} {m B : α → ℕ}
    (pm : Procedure ea unaryCode m) (pb : Procedure ea unaryCode B) :
    Procedure ea unaryCode (fun x => QuantumRawExchange.budgetNat (m x) (B x)) := by
  let c := constant ea
  let s := add pm (mul pm pb)
  exact (add (add (c 1) (mul (c 2000000) s)) (square (mul (c 7056) s))).congrFun
    (by intro x; rfl)

noncomputable opaque rawScaleProgram {α : Type} {ea : α → List Bool} {m B N : α → ℕ}
    (pm : Procedure ea unaryCode m) (pb : Procedure ea unaryCode B)
    (pn : Procedure ea unaryCode N) :
    Procedure ea unaryCode (fun x => QuantumRawExchange.scaleNat (m x) (B x) (N x)) :=
  mul (mul (constant ea 9) (cube (rawBudgetProgram pm pb))) pn

noncomputable opaque rawOutputProgram {α : Type} {ea : α → List Bool} {n m B N : α → ℕ}
    (pc : Procedure ea unaryCode n) (pm : Procedure ea unaryCode m)
    (pb : Procedure ea unaryCode B) (pn : Procedure ea unaryCode N) :
    Procedure ea unaryCode (fun x => QuantumRawExchange.outputNat (n x) (m x) (B x) (N x)) := by
  let c := constant ea
  let r := rawScaleProgram pm pb pn
  exact (add (add (add (mul (add (mul (c 6) pc) (c 1)) (square r))
    (mul (mul (c 3920) r) (add (c 1) pb)))
      (mul (add (mul (c 685600) pm) (c 26000)) pb)) (c 1)).congrFun (by intro x; rfl)

abbrev Input := QuantumCoefficientPrograms.LatticeInput
def inputCode : Input → List Bool := QuantumCoefficientPrograms.latticeInputCode
def value (x : Input) : ℕ := QuantumRawExchange.outputNat
  (x.1+3717*x.2.1) (12544*x.2.1)
  (QuantumOrderedXZ.pipelineNat x.2.1 x.2.2.1 x.2.2.2 6) x.2.2.2

noncomputable opaque program : Procedure inputCode unaryCode value := by
  let n := Procedure.first unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))
  let rest := Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))
  let m := (Procedure.first unaryCode (prodCode unaryCode unaryCode)).comp rest
  let bn := (Procedure.second unaryCode (prodCode unaryCode unaryCode)).comp rest
  let b := (Procedure.first unaryCode unaryCode).comp bn
  let p := (Procedure.second unaryCode unaryCode).comp bn
  exact rawOutputProgram (add n (mul (constant inputCode 3717) m))
    (mul (constant inputCode 12544) m) (logicalProgram m b p 6) p

theorem polynomial_bound : ∃ a : ℕ, ∀ x : Input, value x ≤ (inputCode x).length.succ.succ^a :=
  unaryProcedure_power_bound program

end ContinuumCoulomb.QuantumCoefficientEnvelopeProgram

end

end OAI
