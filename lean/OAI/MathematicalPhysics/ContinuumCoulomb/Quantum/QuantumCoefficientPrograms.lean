import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathIteratedBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingCoefficientBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialUnaryBounds

namespace OAI

/-! Literal unary programs for the actual routing coefficient envelopes.
Their output lengths give polynomial bounds without choosing giant exponents. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientPrograms
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × (ℕ × ℕ)
def inputCode : Input → List Bool := prodCode unaryCode (prodCode unaryCode unaryCode)

def pathBudget (m L : ℕ) : ℕ := 3*m*L+L+3*m*(1+2*L)+4*m*(1+L)^2+1
def pathRadius (m L T : ℕ) : ℕ := L+16*(pathBudget m L)^3*T+4*pathBudget m L+1
def pathCoefficient (m L T : ℕ) : ℕ := 1+L+(7*m+2)*(pathRadius m L T)^2

def iterated (m L T : ℕ) : ℕ → ℕ
  | 0 => L
  | k+1 => pathCoefficient (3^k*m) (iterated m L T k) T

@[simp] theorem pathBudget_cast (m L : ℕ) : (pathBudget m L:ℝ) = qmaPathBudget m L := by
  simp [pathBudget,qmaPathBudget]
@[simp] theorem pathRadius_cast (m L T : ℕ) : (pathRadius m L T:ℝ) = qmaPathRadiusBound m L T := by
  simp [pathRadius,qmaPathRadiusBound]
@[simp] theorem pathCoefficient_cast (m L T : ℕ) :
    (pathCoefficient m L T:ℝ) = qmaPathCoefficientBound m L T := by
  simp [pathCoefficient,qmaPathCoefficientBound]
@[simp] theorem iterated_cast (m L T k : ℕ) :
    (iterated m L T k:ℝ) = qmaPathIteratedBound m L T k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterated,pathCoefficient_cast,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,ih,qmaPathIteratedBound]

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
  (mul p p).congrFun (by intro x; simp only [pow_two])
private noncomputable def cube {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) : Procedure ea unaryCode (fun x => f x^3) :=
  (mul (mul p p) p).congrFun (by intro x; simp only [pow_succ,pow_zero,one_mul])

noncomputable opaque pathBudgetProgram {α : Type} {ea : α → List Bool} {m L : α → ℕ}
    (pm : Procedure ea unaryCode m) (pl : Procedure ea unaryCode L) :
    Procedure ea unaryCode (fun x => pathBudget (m x) (L x)) := by
  let c := constant ea
  exact (add (add (add (add (mul (mul (c 3) pm) pl) pl)
    (mul (mul (c 3) pm) (add (c 1) (mul (c 2) pl))))
    (mul (mul (c 4) pm) (square (add (c 1) pl)))) (c 1)).congrFun (by intro x; rfl)

noncomputable opaque pathRadiusProgram {α : Type} {ea : α → List Bool} {m L T : α → ℕ}
    (pm : Procedure ea unaryCode m) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => pathRadius (m x) (L x) (T x)) := by
  let c := constant ea
  let pb := pathBudgetProgram pm pl
  exact (add (add (add pl (mul (mul (c 16) (cube pb)) pt))
    (mul (c 4) pb)) (c 1)).congrFun (by intro x; rfl)

noncomputable opaque pathCoefficientProgram {α : Type} {ea : α → List Bool} {m L T : α → ℕ}
    (pm : Procedure ea unaryCode m) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => pathCoefficient (m x) (L x) (T x)) := by
  let c := constant ea
  exact (add (add (c 1) pl) (mul (add (mul (c 7) pm) (c 2))
    (square (pathRadiusProgram pm pl pt)))).congrFun (by intro x; rfl)

noncomputable opaque mProgram : Procedure inputCode unaryCode (fun x => x.1) := Procedure.first _ _
noncomputable opaque lProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp (Procedure.second _ _)
noncomputable opaque tProgram : Procedure inputCode unaryCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp (Procedure.second _ _)

noncomputable def iteratedProgram (k : ℕ) :
    Procedure inputCode unaryCode (fun x => iterated x.1 x.2.1 x.2.2 k) := by
  induction k with
  | zero => exact lProgram
  | succ k ih =>
    exact pathCoefficientProgram (mul (constant inputCode (3^k)) mProgram) ih tProgram

theorem iterated_power (k : ℕ) : ∃ a : ℕ, ∀ x : Input,
    iterated x.1 x.2.1 x.2.2 k ≤ ((inputCode x).length+2)^a :=
  unaryProcedure_power_bound (iteratedProgram k)

def crossingBudget (m r L : ℕ) : ℕ := 3*m*L+L+6*r*(1+2*L)+12*r*(1+2*L)^2+1
def crossingRadius (m r L T : ℕ) : ℕ := L+16*(crossingBudget m r L)^3*T+4*crossingBudget m r L+1
def crossingCoefficient (m r L T : ℕ) : ℕ := 1+L+(11*r+2)*(crossingRadius m r L T)^2

@[simp] theorem crossingBudget_cast (m r L : ℕ) :
    (crossingBudget m r L:ℝ) = qmaCrossingBudget m r L := by simp [crossingBudget,qmaCrossingBudget]
@[simp] theorem crossingRadius_cast (m r L T : ℕ) :
    (crossingRadius m r L T:ℝ) = qmaCrossingRadiusBound m r L T := by simp [crossingRadius,qmaCrossingRadiusBound]
@[simp] theorem crossingCoefficient_cast (m r L T : ℕ) :
    (crossingCoefficient m r L T:ℝ) = qmaCrossingCoefficientBound m r L T := by
  simp [crossingCoefficient,qmaCrossingCoefficientBound]

noncomputable opaque crossingBudgetProgram {α : Type} {ea : α → List Bool} {m r L : α → ℕ}
    (pm : Procedure ea unaryCode m) (pr : Procedure ea unaryCode r) (pl : Procedure ea unaryCode L) :
    Procedure ea unaryCode (fun x => crossingBudget (m x) (r x) (L x)) := by
  let c := constant ea
  let p := add (c 1) (mul (c 2) pl)
  exact (add (add (add (add (mul (mul (c 3) pm) pl) pl)
    (mul (mul (c 6) pr) p)) (mul (mul (c 12) pr) (square p))) (c 1)).congrFun (by intro x; rfl)

noncomputable opaque crossingRadiusProgram {α : Type} {ea : α → List Bool} {m r L T : α → ℕ}
    (pm : Procedure ea unaryCode m) (pr : Procedure ea unaryCode r)
    (pl : Procedure ea unaryCode L) (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => crossingRadius (m x) (r x) (L x) (T x)) := by
  let c := constant ea
  let pb := crossingBudgetProgram pm pr pl
  exact (add (add (add pl (mul (mul (c 16) (cube pb)) pt))
    (mul (c 4) pb)) (c 1)).congrFun (by intro x; rfl)

noncomputable opaque crossingCoefficientProgram {α : Type} {ea : α → List Bool} {m r L T : α → ℕ}
    (pm : Procedure ea unaryCode m) (pr : Procedure ea unaryCode r)
    (pl : Procedure ea unaryCode L) (pt : Procedure ea unaryCode T) :
    Procedure ea unaryCode (fun x => crossingCoefficient (m x) (r x) (L x) (T x)) := by
  let c := constant ea
  exact (add (add (c 1) pl) (mul (add (mul (c 11) pr) (c 2))
    (square (crossingRadiusProgram pm pr pl pt)))).congrFun (by intro x; rfl)

end ContinuumCoulomb.QuantumCoefficientPrograms

end

end OAI
