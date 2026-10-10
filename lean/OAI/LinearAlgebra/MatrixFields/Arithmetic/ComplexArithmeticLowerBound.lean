import Mathlib
import OAI.LinearAlgebra.MatrixFields.Tensors.ComplexDotPairing

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Arithmetic

inductive Gate (Input Register : Type*) where
  | constant : ℂ → Gate Input Register
  | input : Input → Gate Input Register
  | add : Register → Register → Gate Input Register
  | sub : Register → Register → Gate Input Register
  | mul : Register → Register → Gate Input Register

namespace Gate

variable {Input Register : Type*}

def eval (inputs : Input → ℂ) (registers : Register → ℂ) : Gate Input Register → ℂ
  | .constant z => z
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

def cost : Gate Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

end Gate

inductive Program (Input : Type*) : ℕ → Type _ where
  | nil : Program Input 0
  | step {r : ℕ} : Program Input r → Gate Input (Fin r) → Program Input (r + 1)

namespace Program

variable {Input : Type*}

def eval : {r : ℕ} → Program Input r → (Input → ℂ) → Fin r → ℂ
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
    Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)

def cost : {r : ℕ} → Program Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

@[simp] theorem eval_step_zero {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

@[simp] theorem cost_step {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

abbrev MatrixInput (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

def matrixInputs {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : MatrixInput n → ℂ
  | .inl (i, j) => A i j
  | .inr (j, k) => B j k

structure MatrixAlgorithm (n : ℕ) where
  registers : ℕ
  program : Program (MatrixInput n) registers
  output : Fin n → Fin n → Fin registers

namespace MatrixAlgorithm

def eval {n : ℕ} (P : MatrixAlgorithm n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => P.program.eval (matrixInputs A B) (P.output i k)

def Correct {n : ℕ} (P : MatrixAlgorithm n) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℂ, P.eval A B = A * B

def cost {n : ℕ} (P : MatrixAlgorithm n) : ℕ := P.program.cost

theorem correct_iff_entries {n : ℕ} (P : MatrixAlgorithm n) :
    P.Correct ↔ ∀ (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

def scalarAlgorithm : MatrixAlgorithm 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

theorem scalarAlgorithm_correct : scalarAlgorithm.Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

@[simp] theorem scalarAlgorithm_cost : scalarAlgorithm.cost = 1 := rfl

def AdmissibleExponent (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

noncomputable def omega : ℝ := sInf {τ : ℝ | AdmissibleExponent τ}

end Arithmetic

namespace Tensor

def matrixMultiplication (a b c : ℕ) :
    Tensor ℂ (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

@[simp] theorem matrixMultiplication_matching (a b c : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    matrixMultiplication a b c (i, j) (j, k) (k, i) = 1 := by
  simp [matrixMultiplication]

end Tensor
end MatrixMultiplication.Foundation

end

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Gate

variable {Input R S : Type*}

def mapRegister (f : R → S) : Gate Input R → Gate Input S
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .mul i j => .mul (f i) (f j)

theorem eval_mapRegister (g : Gate Input R) (f : R → S)
    (inputs : Input → ℂ) (registers : S → ℂ) :
    (g.mapRegister f).eval inputs registers = g.eval inputs (fun i => registers (f i)) := by
  cases g <;> rfl

@[simp] theorem cost_mapRegister (g : Gate Input R) (f : R → S) :
    (g.mapRegister f).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {Input : Type*}

def oldIndex (r s : ℕ) (i : Fin r) : Fin (r + s) := ⟨s + i.val, by omega⟩

def newIndex (r s : ℕ) (i : Fin s) : Fin (r + s) := ⟨i.val, by omega⟩

@[simp] theorem oldIndex_zero (r : ℕ) (i : Fin r) : oldIndex r 0 i = i := by
  apply Fin.ext
  simp [oldIndex]

@[simp] theorem oldIndex_succ (r s : ℕ) (i : Fin r) :
    oldIndex r (s + 1) i = (oldIndex r s i).succ := by
  apply Fin.ext
  simp only [oldIndex, Fin.val_succ]
  omega

@[simp] theorem newIndex_zero (r s : ℕ) : newIndex r (s + 1) 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem newIndex_succ (r s : ℕ) (i : Fin s) :
    newIndex r (s + 1) i.succ = (newIndex r s i).succ := by
  apply Fin.ext
  rfl

def append {r : ℕ} (p : Program Input r) : {s : ℕ} → Program Input s → Program Input (r + s)
  | 0, .nil => p
  | s + 1, .step q g => (p.append q).step (g.mapRegister (newIndex r s))

theorem eval_append_new {r s : ℕ} (p : Program Input r) (q : Program Input s)
    (inputs : Input → ℂ) :
    ∀ i : Fin s, (p.append q).eval inputs (newIndex r s i) = q.eval inputs i := by
  induction q with
  | nil => intro i; exact Fin.elim0 i
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [append, newIndex_zero, eval_step_zero, Gate.eval_mapRegister]
      rw [funext ih]
    · simpa only [append, newIndex_succ, eval_step_succ] using ih j

theorem eval_append_old {r s : ℕ} (p : Program Input r) (q : Program Input s)
    (inputs : Input → ℂ) :
    ∀ i : Fin r, (p.append q).eval inputs (oldIndex r s i) = p.eval inputs i := by
  induction q with
  | nil => intro i; simp [append]
  | @step s q g ih =>
    intro i
    simpa only [append, oldIndex_succ, eval_step_succ] using ih i

@[simp] theorem cost_append {r s : ℕ} (p : Program Input r) (q : Program Input s) :
    (p.append q).cost = p.cost + q.cost := by
  induction q with
  | nil => simp [append, cost]
  | @step s q g ih => simp [append, ih, Nat.add_assoc]

end Program

inductive Expression (Input : Type*) where
  | constant : ℂ → Expression Input
  | input : Input → Expression Input
  | add : Expression Input → Expression Input → Expression Input
  | sub : Expression Input → Expression Input → Expression Input
  | mul : Expression Input → Expression Input → Expression Input

namespace Expression

variable {Input : Type*}

def eval (inputs : Input → ℂ) : Expression Input → ℂ
  | .constant z => z
  | .input i => inputs i
  | .add e f => e.eval inputs + f.eval inputs
  | .sub e f => e.eval inputs - f.eval inputs
  | .mul e f => e.eval inputs * f.eval inputs

def cost : Expression Input → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add e f => e.cost + f.cost + 1
  | .sub e f => e.cost + f.cost + 1
  | .mul e f => e.cost + f.cost + 1

structure Compiled (e : Expression Input) where
  registers : ℕ
  program : Program Input registers
  output : Fin registers
  correct : ∀ inputs, program.eval inputs output = e.eval inputs
  cost_eq : program.cost = e.cost

def compile : (e : Expression Input) → Compiled e
  | .constant z =>
    { registers := 1
      program := Program.nil.step (.constant z)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .input i =>
    { registers := 1
      program := Program.nil.step (.input i)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .add e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.add (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .sub e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.sub (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .mul e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.mul (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }

end Expression

namespace Gate

variable {Input Input' Register : Type*}

def mapInput (f : Input → Input') : Gate Input Register → Gate Input' Register
  | .constant z => .constant z
  | .input i => .input (f i)
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapInput (f : Input → Input') (g : Gate Input Register)
    (inputs : Input' → ℂ) (registers : Register → ℂ) :
    (g.mapInput f).eval inputs registers = g.eval (inputs ∘ f) registers := by
  cases g <;> rfl

@[simp] theorem cost_mapInput (f : Input → Input') (g : Gate Input Register) :
    (g.mapInput f).cost = g.cost := by
  cases g <;> rfl

def mapSource (f : Input → Input' ⊕ ℂ) : Gate Input Register → Gate Input' Register
  | .constant z => .constant z
  | .input i => match f i with
    | .inl j => .input j
    | .inr z => .constant z
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ ℂ) (g : Gate Input Register)
    (inputs : Input' → ℂ) (registers : Register → ℂ) :
    (g.mapSource f).eval inputs registers =
      g.eval (fun i => Sum.elim inputs id (f i)) registers := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, eval]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

@[simp] theorem cost_mapSource (f : Input → Input' ⊕ ℂ) (g : Gate Input Register) :
    (g.mapSource f).cost = g.cost := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, cost]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

end Gate

namespace Program

variable {Input Input' Mid : Type*}

def mapInput (f : Input → Input') : {r : ℕ} → Program Input r → Program Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapInput f).step (g.mapInput f)

@[simp] theorem eval_mapInput (f : Input → Input') {r : ℕ} (p : Program Input r)
    (inputs : Input' → ℂ) :
    ∀ i : Fin r, (p.mapInput f).eval inputs i = p.eval (inputs ∘ f) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapInput, eval_step_zero, Gate.eval_mapInput]
      rw [funext ih]
    · exact ih j

@[simp] theorem cost_mapInput (f : Input → Input') {r : ℕ} (p : Program Input r) :
    (p.mapInput f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapInput, cost_step, Gate.cost_mapInput, ih]

def mapSource (f : Input → Input' ⊕ ℂ) : {r : ℕ} → Program Input r → Program Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapSource f).step (g.mapSource f)

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ ℂ) {r : ℕ}
    (p : Program Input r) (inputs : Input' → ℂ) :
    ∀ i : Fin r, (p.mapSource f).eval inputs i =
      p.eval (fun j => Sum.elim inputs id (f j)) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapSource, eval_step_zero, Gate.eval_mapSource]
      rw [funext ih]
    · exact ih j

@[simp] theorem cost_mapSource (f : Input → Input' ⊕ ℂ) {r : ℕ}
    (p : Program Input r) : (p.mapSource f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapSource, cost_step, Gate.cost_mapSource, ih]

structure Substituted {r s : ℕ} (p : Program Input r) (q : Program Mid s)
    (wires : Mid → Fin r) where
  registers : ℕ
  program : Program Input registers
  oldOutput : Fin r → Fin registers
  output : Fin s → Fin registers
  correctOld : ∀ inputs i, program.eval inputs (oldOutput i) = p.eval inputs i
  correct : ∀ inputs i, program.eval inputs (output i) =
    q.eval (fun j => p.eval inputs (wires j)) i
  cost_eq : program.cost = p.cost + q.cost

namespace Substituted

def step {r s : ℕ} {p : Program Input r} {q : Program Mid s}
    {wires : Mid → Fin r} (a : Substituted p q wires)
    (g : Gate Mid (Fin s)) (h : Gate Input (Fin a.registers))
    (heval : ∀ inputs, h.eval inputs (a.program.eval inputs) =
      g.eval (fun j => p.eval inputs (wires j))
        (q.eval (fun j => p.eval inputs (wires j))))
    (hcost : h.cost = g.cost) : Substituted p (q.step g) wires where
  registers := a.registers + 1
  program := a.program.step h
  oldOutput := fun i => (a.oldOutput i).succ
  output := Fin.cases 0 (fun i => (a.output i).succ)
  correctOld := by
    intro inputs i
    exact a.correctOld inputs i
  correct := by
    intro inputs i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact heval inputs
    · exact a.correct inputs j
  cost_eq := by
    simp only [cost_step, a.cost_eq, hcost, Nat.add_assoc]

end Substituted

def substitute {r : ℕ} (p : Program Input r) :
    {s : ℕ} → (q : Program Mid s) → (wires : Mid → Fin r) → Substituted p q wires
  | 0, .nil, wires =>
    { registers := r
      program := p
      oldOutput := id
      output := Fin.elim0
      correctOld := fun _ _ => rfl
      correct := fun _ i => Fin.elim0 i
      cost_eq := by simp only [cost, Nat.add_zero] }
  | _ + 1, .step q g, wires =>
    let a := substitute p q wires
    match g with
    | .input j =>
      { registers := a.registers
        program := a.program
        oldOutput := a.oldOutput
        output := Fin.cases (a.oldOutput (wires j)) a.output
        correctOld := a.correctOld
        correct := by
          intro inputs i
          refine Fin.cases ?_ (fun k => ?_) i
          · exact a.correctOld inputs (wires j)
          · exact a.correct inputs k
        cost_eq := by
          simpa only [cost_step, Gate.cost, Nat.add_zero] using a.cost_eq }
    | .constant z =>
      a.step (.constant z) (.constant z) (fun _ => rfl) rfl
    | .add i j =>
      a.step (.add i j) (.add (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .sub i j =>
      a.step (.sub i j) (.sub (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .mul i j =>
      a.step (.mul i j) (.mul (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl

end Program

end MatrixMultiplication.Foundation.Arithmetic

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic

def zeroPadMatrix {n : ℕ} (m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if hi : i.val < n then
    if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else 0

@[simp] theorem zeroPadMatrix_castLE {n m : ℕ} (h : n ≤ m)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    zeroPadMatrix m A (Fin.castLE h i) (Fin.castLE h j) = A i j := by
  simp [zeroPadMatrix, i.is_lt, j.is_lt]

theorem sum_fin_castLE_of_zero {n m : ℕ} (h : n ≤ m) (f : Fin m → ℂ)
    (hf : ∀ j : Fin m, n ≤ j.val → f j = 0) :
    (∑ j : Fin m, f j) = ∑ j : Fin n, f (Fin.castLE h j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) ?_
    (fun j : Fin n => f (Fin.castLE h j)) f ?_ (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (congrArg (fun v : Fin m => v.val) hij)
  · intro j hj
    exact hf j (le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩)

theorem zeroPadMatrix_mul {n m : ℕ} (h : n ≤ m)
    (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) :
    (zeroPadMatrix m A * zeroPadMatrix m B) (Fin.castLE h i) (Fin.castLE h k) =
      (A * B) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    (∑ j : Fin m,
        zeroPadMatrix m A (Fin.castLE h i) j *
          zeroPadMatrix m B j (Fin.castLE h k)) =
        ∑ j : Fin n,
          zeroPadMatrix m A (Fin.castLE h i) (Fin.castLE h j) *
            zeroPadMatrix m B (Fin.castLE h j) (Fin.castLE h k) := by
      apply sum_fin_castLE_of_zero h
      intro j hj
      simp [zeroPadMatrix, not_lt_of_ge hj]
    _ = ∑ j : Fin n, A i j * B j k := by simp

def padSource {n m : ℕ} : MatrixInput m → MatrixInput n ⊕ ℂ
  | .inl (i, j) => if hi : i.val < n then
      if hj : j.val < n then .inl (.inl (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0
  | .inr (i, j) => if hi : i.val < n then
      if hj : j.val < n then .inl (.inr (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0

theorem padSource_eval {n m : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (fun x : MatrixInput m => Sum.elim (matrixInputs A B) id (padSource x)) =
      matrixInputs (zeroPadMatrix m A) (zeroPadMatrix m B) := by
  funext x
  rcases x with ⟨i, j⟩ | ⟨i, j⟩
  all_goals
    by_cases hi : i.val < n <;> by_cases hj : j.val < n <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hi, hj]

namespace MatrixAlgorithm

def pad {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m) : MatrixAlgorithm n where
  registers := P.registers
  program := P.program.mapSource (padSource (n := n))
  output := fun i k => P.output (Fin.castLE h i) (Fin.castLE h k)

theorem pad_correct {n m : ℕ} (h : n ≤ m) {P : MatrixAlgorithm m}
    (hP : P.Correct) : (pad h P).Correct := by
  intro A B
  funext i k
  change (P.program.mapSource (padSource (n := n))).eval (matrixInputs A B)
    (P.output (Fin.castLE h i) (Fin.castLE h k)) = (A * B) i k
  rw [Program.eval_mapSource, padSource_eval]
  have hentry := congrFun (congrFun
    (hP (zeroPadMatrix m A) (zeroPadMatrix m B)) (Fin.castLE h i)) (Fin.castLE h k)
  exact hentry.trans (zeroPadMatrix_mul h A B i k)

@[simp] theorem pad_cost_eq {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m) :
    (pad h P).cost = P.cost :=
  Program.cost_mapSource (padSource (n := n)) P.program

theorem exists_restrict {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m)
    (hP : P.Correct) : ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost :=
  ⟨pad h P, pad_correct h hP, (pad_cost_eq h P).le⟩

end MatrixAlgorithm

end MatrixMultiplication.Foundation.Arithmetic

end

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Program

theorem eval_eq_constant_or_input_of_cost_eq_zero {Input : Type*} {r : ℕ}
    (p : Program Input r) (hp : p.cost = 0) (i : Fin r) :
    (∃ z : ℂ, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  revert hp i
  induction p with
  | nil =>
    intro _ i
    exact Fin.elim0 i
  | @step r p g ih =>
    intro hp i
    have hcost : p.cost + g.cost = 0 := hp
    have hp0 : p.cost = 0 := by omega
    have hg0 : g.cost = 0 := by omega
    refine Fin.cases ?_ (fun j => ?_) i
    · cases g with
      | constant z => exact Or.inl ⟨z, fun _ => rfl⟩
      | input a => exact Or.inr ⟨a, fun _ => rfl⟩
      | add a b => simp [Gate.cost] at hg0
      | sub a b => simp [Gate.cost] at hg0
      | mul a b => simp [Gate.cost] at hg0
    · simpa only [eval_step_succ] using ih hp0 j

end Program

namespace MatrixAlgorithm

theorem one_le_cost {n : ℕ} (P : MatrixAlgorithm n) (hn : 1 ≤ n)
    (hP : P.Correct) : 1 ≤ P.cost := by
  by_contra hcost
  have hzero : P.program.cost = 0 := by
    change ¬ 1 ≤ P.program.cost at hcost
    omega
  let i : Fin n := ⟨0, by omega⟩
  have hentry (A B : Matrix (Fin n) (Fin n) ℂ) :
      P.program.eval (matrixInputs A B) (P.output i i) = (A * B) i i :=
    congrFun (congrFun (hP A B) i) i
  rcases P.program.eval_eq_constant_or_input_of_cost_eq_zero hzero (P.output i i)
      with ⟨z, hz⟩ | ⟨a, ha⟩
  · have hz0 : z = 0 := by
      have h := hentry 0 0
      rw [hz] at h
      simpa using h
    have hz1 : z = 1 := by
      have h := hentry 1 1
      rw [hz] at h
      simpa using h
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (hz0.symm.trans hz1)
  · rcases a with ⟨j, k⟩ | ⟨j, k⟩
    · have h := hentry (fun _ _ => 1) 0
      rw [ha] at h
      change (1 : ℂ) = ∑ index : Fin n, (1 : ℂ) * 0 at h
      simp at h
    · have h := hentry 0 (fun _ _ => 1)
      rw [ha] at h
      change (1 : ℂ) = ∑ index : Fin n, (0 : ℂ) * 1 at h
      simp at h

end MatrixAlgorithm

theorem admissibleExponent_nonneg {τ : ℝ} (hτ : AdmissibleExponent τ) : 0 ≤ τ := by
  by_contra hneg
  have hτneg : τ < 0 := lt_of_not_ge hneg
  let ε : ℝ := -τ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hsum : τ + ε = -ε := by dsimp [ε]; ring
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hcostone : (1 : ℝ) ≤ P.cost :=
    (Nat.one_le_cast (α := ℝ)).mpr (P.one_le_cost hn1 hP)
  rw [hsum, Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv] at hcost
  have hsmall : C / (n : ℝ) ^ ε < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hnpos ε)).mpr hpow
  exact (not_lt_of_ge (hcostone.trans hcost)) hsmall

theorem admissibleExponent_bddBelow : BddBelow {τ : ℝ | AdmissibleExponent τ} := by
  refine ⟨0, ?_⟩
  intro τ hτ
  exact admissibleExponent_nonneg hτ

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixAllFields

end OAI
