import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity
import OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Exponent

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

namespace Gate

variable {Input Register : Type*}

def toLegacy : Gate ℂ Input Register → MatrixMultiplication.Foundation.Arithmetic.Gate Input Register
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

def ofLegacy : MatrixMultiplication.Foundation.Arithmetic.Gate Input Register → Gate ℂ Input Register
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_toLegacy (g : Gate ℂ Input Register)
    (inputs : Input → ℂ) (registers : Register → ℂ) :
    g.toLegacy.eval inputs registers = g.eval inputs registers := by
  cases g <;> rfl

@[simp] theorem cost_toLegacy (g : Gate ℂ Input Register) : g.toLegacy.cost = g.cost := by
  cases g <;> rfl

@[simp] theorem eval_ofLegacy (g : MatrixMultiplication.Foundation.Arithmetic.Gate Input Register)
    (inputs : Input → ℂ) (registers : Register → ℂ) :
    (ofLegacy g).eval inputs registers = g.eval inputs registers := by
  cases g <;> rfl

@[simp] theorem cost_ofLegacy (g : MatrixMultiplication.Foundation.Arithmetic.Gate Input Register) :
    (ofLegacy g).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {Input : Type*}

def toLegacy : {r : ℕ} → Program ℂ Input r → MatrixMultiplication.Foundation.Arithmetic.Program Input r
  | 0, .nil => .nil
  | _ + 1, .step p g => p.toLegacy.step g.toLegacy

def ofLegacy : {r : ℕ} → MatrixMultiplication.Foundation.Arithmetic.Program Input r → Program ℂ Input r
  | 0, .nil => .nil
  | _ + 1, .step p g => (ofLegacy p).step (Gate.ofLegacy g)

@[simp] theorem eval_toLegacy {r : ℕ} (p : Program ℂ Input r) (inputs : Input → ℂ) :
    p.toLegacy.eval inputs = p.eval inputs := by
  induction p with
  | nil => rfl
  | step p g ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [toLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_zero,
        eval_step_zero, Gate.eval_toLegacy, ih]
    · simp only [toLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_succ,
        eval_step_succ, ih]

@[simp] theorem cost_toLegacy {r : ℕ} (p : Program ℂ Input r) : p.toLegacy.cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [toLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.cost_step,
      cost_step, Gate.cost_toLegacy, ih]

@[simp] theorem eval_ofLegacy {r : ℕ}
    (p : MatrixMultiplication.Foundation.Arithmetic.Program Input r) (inputs : Input → ℂ) :
    (ofLegacy p).eval inputs = p.eval inputs := by
  induction p with
  | nil => rfl
  | step p g ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [ofLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_zero,
        eval_step_zero, Gate.eval_ofLegacy, ih]
    · simp only [ofLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.eval_step_succ,
        eval_step_succ, ih]

@[simp] theorem cost_ofLegacy {r : ℕ}
    (p : MatrixMultiplication.Foundation.Arithmetic.Program Input r) : (ofLegacy p).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [ofLegacy, MatrixMultiplication.Foundation.Arithmetic.Program.cost_step,
      cost_step, Gate.cost_ofLegacy, ih]

end Program

namespace MatrixAlgorithm

def toLegacy {n : ℕ} (P : MatrixAlgorithm ℂ n n n) :
    MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n :=
  ⟨P.registers, P.program.toLegacy, P.output⟩

def ofLegacy {n : ℕ} (P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n) :
    MatrixAlgorithm ℂ n n n :=
  ⟨P.registers, Program.ofLegacy P.program, P.output⟩

@[simp] theorem eval_toLegacy {n : ℕ} (P : MatrixAlgorithm ℂ n n n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : P.toLegacy.eval A B = P.eval A B := by
  funext i k
  have hin : MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B = matrixInputs A B := by
    funext x
    cases x <;> rfl
  change P.program.toLegacy.eval (MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B)
    (P.output i k) = P.program.eval (matrixInputs A B) (P.output i k)
  rw [hin]
  exact congrFun (P.program.eval_toLegacy (matrixInputs A B)) (P.output i k)

@[simp] theorem eval_ofLegacy {n : ℕ}
    (P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : (ofLegacy P).eval A B = P.eval A B := by
  funext i k
  have hin : MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B = matrixInputs A B := by
    funext x
    cases x <;> rfl
  change (Program.ofLegacy P.program).eval (matrixInputs A B) (P.output i k) =
    P.program.eval (MatrixMultiplication.Foundation.Arithmetic.matrixInputs A B) (P.output i k)
  rw [hin]
  exact congrFun (Program.eval_ofLegacy P.program (matrixInputs A B)) (P.output i k)

theorem toLegacy_correct {n : ℕ} {P : MatrixAlgorithm ℂ n n n}
    (hP : P.Correct) : P.toLegacy.Correct := by
  intro A B
  exact (P.eval_toLegacy A B).trans (hP A B)

theorem ofLegacy_correct {n : ℕ} {P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n}
    (hP : P.Correct) : (ofLegacy P).Correct := by
  intro A B
  exact (eval_ofLegacy P A B).trans (hP A B)

@[simp] theorem cost_toLegacy {n : ℕ} (P : MatrixAlgorithm ℂ n n n) :
    P.toLegacy.cost = P.cost := P.program.cost_toLegacy

@[simp] theorem cost_ofLegacy {n : ℕ}
    (P : MatrixMultiplication.Foundation.Arithmetic.MatrixAlgorithm n) :
    (ofLegacy P).cost = P.cost := Program.cost_ofLegacy P.program

end MatrixAlgorithm

theorem complex_admissibleExponent_iff (τ : ℝ) :
    AdmissibleExponent ℂ τ ↔ MatrixMultiplication.Foundation.Arithmetic.AdmissibleExponent τ := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    obtain ⟨P, hP, hcost⟩ := hbound n hn
    exact ⟨P.toLegacy, MatrixAlgorithm.toLegacy_correct hP, by simpa using hcost⟩
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    obtain ⟨P, hP, hcost⟩ := hbound n hn
    exact ⟨MatrixAlgorithm.ofLegacy P, MatrixAlgorithm.ofLegacy_correct hP,
      by simpa using hcost⟩

theorem complex_omega_eq : omega ℂ = MatrixMultiplication.Foundation.Arithmetic.omega := by
  unfold omega MatrixMultiplication.Foundation.Arithmetic.omega
  congr 1
  ext τ
  exact complex_admissibleExponent_iff τ

end MatrixMultiplication.Arithmetic

end

end OAI
