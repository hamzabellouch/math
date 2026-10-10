import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListOutputBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCoefficientPrograms

namespace OAI

/-! Literal unary programs compute the coefficient envelopes. For each fixed
number of rounds, the complete numerical envelope is polynomial in its inputs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

def budgetNat (M L : ℕ) : ℕ := 3*M*L+L+3*M*(1+4*L)+12*M*(1+2*L)^2+1
def radiusNat (M L T : ℕ) : ℕ := L+16*(budgetNat M L)^3*T+4*budgetNat M L+1
def coefficientNat (M L T : ℕ) : ℕ := 1+L+(10*M+2)*(radiusNat M L T)^2
def envelopeNat (M L T : ℕ) : ℕ → ℕ
  | 0 => L
  | k+1 => coefficientNat M (envelopeNat M L T k) T

@[simp] theorem budgetNat_cast (M L : ℕ) : (budgetNat M L:ℝ)=forkBudget M L := by
  simp [budgetNat,forkBudget]
@[simp] theorem radiusNat_cast (M L T : ℕ) : (radiusNat M L T:ℝ)=forkRadius M L T := by
  simp [radiusNat,forkRadius]
@[simp] theorem coefficientNat_cast (M L T : ℕ) :
    (coefficientNat M L T:ℝ)=forkCoefficient M L T := by
  simp [coefficientNat,forkCoefficient]
@[simp] theorem envelopeNat_cast (M L T k : ℕ) :
    (envelopeNat M L T k:ℝ)=coefficientEnvelope M L T k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [envelopeNat,coefficientNat_cast,ih,coefficientEnvelope]

private noncomputable def add {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x+g x) := Procedure.unaryAdd.comp (p.pair q)
private noncomputable def mul {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x*g x) := Procedure.unaryMul.comp (p.pair q)
private noncomputable def konst {α : Type} (ea : α → List Bool) (n : ℕ) :
    Procedure ea unaryCode (fun _ => n) := Procedure.constant ea unaryCode n
private noncomputable def sq {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^2) :=
  (mul p p).congrFun (by intro x; simp only [pow_two])
private noncomputable def cube {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^3) :=
  (mul (mul p p) p).congrFun (by intro x; simp only [pow_succ,pow_zero,one_mul])

noncomputable def budgetNatProgram {α : Type} {ea : α → List Bool} {M L : α → ℕ}
    (pm : Procedure ea unaryCode M) (pl : Procedure ea unaryCode L) :
    Procedure ea unaryCode (fun x => budgetNat (M x) (L x)) := by
  let c := konst ea
  exact (add (add (add (add (mul (mul (c 3) pm) pl) pl)
    (mul (mul (c 3) pm) (add (c 1) (mul (c 4) pl))))
    (mul (mul (c 12) pm) (sq (add (c 1) (mul (c 2) pl))))) (c 1)).congrFun
      (by intro x; rfl)

noncomputable def radiusNatProgram {α : Type} {ea : α → List Bool} {M L T : α → ℕ}
    (pm : Procedure ea unaryCode M) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => radiusNat (M x) (L x) (T x)) := by
  let c := konst ea
  let pb := budgetNatProgram pm pl
  exact (add (add (add pl (mul (mul (c 16) (cube pb)) pt)) (mul (c 4) pb)) (c 1)).congrFun
    (by intro x; rfl)

noncomputable def coefficientNatProgram {α : Type} {ea : α → List Bool} {M L T : α → ℕ}
    (pm : Procedure ea unaryCode M) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => coefficientNat (M x) (L x) (T x)) := by
  let c := konst ea
  exact (add (add (c 1) pl) (mul (add (mul (c 10) pm) (c 2))
    (sq (radiusNatProgram pm pl pt)))).congrFun (by intro x; rfl)

noncomputable def envelopeNatProgram (k : ℕ) {α : Type} {ea : α → List Bool} {M L T : α → ℕ}
    (pm : Procedure ea unaryCode M) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => envelopeNat (M x) (L x) (T x) k) := by
  induction k with
  | zero => exact pl
  | succ k ih => exact coefficientNatProgram pm ih pt

theorem envelopeNat_power (k : ℕ) : ∃ a : ℕ, ∀ x : QuantumCoefficientPrograms.Input,
    envelopeNat x.1 x.2.1 x.2.2 k ≤ ((QuantumCoefficientPrograms.inputCode x).length+2)^a :=
  unaryProcedure_power_bound (envelopeNatProgram k QuantumCoefficientPrograms.mProgram
    QuantumCoefficientPrograms.lProgram QuantumCoefficientPrograms.tProgram)

def outputCoefficientNat (m D L T : ℕ) : ℕ :=
  let M := (8*D+3)*m
  envelopeNat M (coefficientNat M L T) T D

@[simp] theorem outputCoefficientNat_cast (m D L T : ℕ) :
    (outputCoefficientNat m D L T:ℝ)=outputCoefficient m D L T := by
  simp only [outputCoefficientNat,envelopeNat_cast,coefficientNat_cast,outputCoefficient]

noncomputable def outputCoefficientNatProgram (D : ℕ) :
    Procedure QuantumCoefficientPrograms.inputCode unaryCode
      (fun x => outputCoefficientNat x.1 D x.2.1 x.2.2) := by
  let pm := mul (konst QuantumCoefficientPrograms.inputCode (8*D+3))
    QuantumCoefficientPrograms.mProgram
  let pl := coefficientNatProgram pm QuantumCoefficientPrograms.lProgram QuantumCoefficientPrograms.tProgram
  exact envelopeNatProgram D pm pl QuantumCoefficientPrograms.tProgram

theorem outputCoefficientNat_power (D : ℕ) : ∃ a : ℕ, ∀ x : QuantumCoefficientPrograms.Input,
    outputCoefficientNat x.1 D x.2.1 x.2.2 ≤ ((QuantumCoefficientPrograms.inputCode x).length+2)^a :=
  unaryProcedure_power_bound (outputCoefficientNatProgram D)

end ContinuumCoulomb.QuantumForkList

end

end OAI
