import Mathlib
import OAI.Computability.QuantumFactoring.CircuitSemantics
import OAI.Computability.QuantumFactoring.BooleanCircuit

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators

lemma programMatrix_nil {q : ℕ} : programMatrix ([] : List (Instruction q)) = 1 := rfl

lemma programMatrix_cons {q : ℕ} (o : Instruction q) (ops : List (Instruction q)) :
    programMatrix (o :: ops) = programMatrix ops * o.matrix := by
  change ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * 1) = _
  rw [programMatrix_fold, Matrix.mul_one]

lemma programMatrix_singleton {q : ℕ} (o : Instruction q) :
    programMatrix [o] = o.matrix := by
  rw [programMatrix_cons, programMatrix_nil, Matrix.one_mul]

/-- A Boolean node is implemented by at most two of the named fixed gates.
The target is excluded from the sources, but repeated sources are permitted.
Its action toggles the target, so the semantics are reversible on all states. -/
inductive BooleanOp (q : ℕ) (t : Fin q) where
  | constant (b : Bool)
  | copy (a : Fin q) (ha : a ≠ t)
  | neg (a : Fin q) (ha : a ≠ t)
  | conj (a b : Fin q) (ha : a ≠ t) (hb : b ≠ t)

namespace BooleanOp

def value {q : ℕ} {t : Fin q} : BooleanOp q t → Basis q → Bool
  | .constant b, _ => b
  | .copy a _, x => x a
  | .neg a _, x => !x a
  | .conj a b _ _, x => x a && x b

def eval {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) : Basis q :=
  Function.update x t (Bool.xor (x t) (o.value x))

def compile {q : ℕ} {t : Fin q} : BooleanOp q t → List (Instruction q)
  | .constant false => []
  | .constant true => [notAt t]
  | .copy a ha => [cnotAt a t ha]
  | .neg a ha => [cnotAt a t ha, notAt t]
  | .conj a b ha hb => if h : a = b then [cnotAt a t ha]
      else [toffoliAt a b t h ha hb]

lemma compile_length {q : ℕ} {t : Fin q} (o : BooleanOp q t) :
    o.compile.length ≤ 2 := by
  cases o with
  | constant b => cases b <;> simp [compile]
  | copy => simp [compile]
  | neg => simp [compile]
  | conj a b ha hb => simp only [compile]; split <;> simp

lemma eval_at {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) :
    o.eval x t = Bool.xor (x t) (o.value x) := Function.update_self _ _ _

lemma eval_away {q : ℕ} {t i : Fin q} (o : BooleanOp q t) (x : Basis q) (hi : i ≠ t) :
    o.eval x i = x i := Function.update_of_ne hi _ _

lemma eval_fresh {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) (ht : x t = false) :
    o.eval x = Function.update x t (o.value x) := by
  simp [eval, ht]

lemma compile_basis {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) :
    (programMatrix o.compile).mulVec (basisVector x) = basisVector (o.eval x) := by
  cases o with
  | constant b =>
    cases b
    · simp [compile, programMatrix_nil, eval, value]
    · rw [compile, programMatrix_singleton, notAt_basis]
      simp [eval, value]
  | copy a ha =>
    rw [compile, programMatrix_singleton, cnotAt_basis]
    simp [eval, value, Bool.xor_comm]
  | neg a ha =>
    rw [compile, programMatrix_cons, programMatrix_singleton, ← Matrix.mulVec_mulVec,
      cnotAt_basis, notAt_basis]
    congr 1
    simp only [Function.update_self, Function.update_idem, eval, value]
    congr 1
    cases x a <;> cases x t <;> rfl
  | conj a b ha hb =>
    simp only [compile]
    split_ifs with hab
    · rw [programMatrix_singleton, cnotAt_basis]
      subst b
      simp [eval, value, Bool.xor_comm]
    · rw [programMatrix_singleton, toffoliAt_basis]
      rfl

end BooleanOp

/-- The classical network explicitly retains all values already computed.
In a fresh-output DAG each node's target is a previously zero ancilla. -/
abbrev BooleanProgram (q : ℕ) := List ((t : Fin q) × BooleanOp q t)

def BooleanProgram.eval {q : ℕ} (p : BooleanProgram q) (x : Basis q) : Basis q :=
  p.foldl (fun x o => o.2.eval x) x

def BooleanProgram.compile {q : ℕ} (p : BooleanProgram q) : List (Instruction q) :=
  p.flatMap (fun o => o.2.compile)

lemma BooleanProgram.compile_basis {q : ℕ} (p : BooleanProgram q) (x : Basis q) :
    (programMatrix p.compile).mulVec (basisVector x) = basisVector (p.eval x) := by
  induction p generalizing x with
  | nil => simp [compile, eval, programMatrix_nil]
  | cons o p ih =>
    change (programMatrix (o.2.compile ++ BooleanProgram.compile p)).mulVec (basisVector x) = _
    rw [programMatrix_append, ← Matrix.mulVec_mulVec, BooleanOp.compile_basis, ih]
    rfl

lemma BooleanProgram.compile_length {q : ℕ} (p : BooleanProgram q) :
    p.compile.length ≤ 2 * p.length := by
  induction p with
  | nil => simp [compile]
  | cons o p ih =>
    change (o.2.compile ++ BooleanProgram.compile p).length ≤ 2 * (o :: p).length
    rw [List.length_append, List.length_cons]
    have h := o.2.compile_length
    omega

/-- Reversing the actual compiled gate list erases the complete retained trace,
not only its output. No irreversible erasure is used. -/
lemma BooleanProgram.uncompute {q : ℕ} (p : BooleanProgram q) (x : Basis q) :
    (programMatrix (p.compile.reverse.map Instruction.reverse)).mulVec
      (basisVector (p.eval x)) = basisVector x := by
  rw [← p.compile_basis x, programMatrix_reverse, Matrix.mulVec_mulVec,
    Matrix.mem_unitaryGroup_iff'.mp (programMatrix_unitary _), Matrix.one_mulVec]

end ExactQuantumFactoring


end

end OAI
