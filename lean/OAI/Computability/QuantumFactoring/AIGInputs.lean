import Mathlib

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGCompiler
open Std.Sat

/-- One real AIG atom per input bit. The initial graph has one false node. -/
def inputsPrefix (n : ℕ) : (k : ℕ) → k ≤ n →
    (g : AIG (Fin n)) × (Fin k → AIG.Ref g)
  | 0, _ => ⟨AIG.empty, Fin.elim0⟩
  | k+1, h =>
    let old := inputsPrefix n k (by omega)
    let res := old.1.mkAtom ⟨k, by omega⟩
    ⟨res.aig, Fin.snoc (fun i => (old.2 i).cast (AIG.LawfulOperator.le_size (f := AIG.mkAtom) old.1 (⟨k, by omega⟩ : Fin n))) res.ref⟩

lemma inputsPrefix_size (n k : ℕ) (h : k ≤ n) : (inputsPrefix n k h).1.decls.size = k+1 := by
  induction k with
  | zero => simp [inputsPrefix, AIG.empty]
  | succ k ih => simp [inputsPrefix, AIG.mkAtom, ih]

lemma inputsPrefix_correct (n k : ℕ) (h : k ≤ n) (x : Fin n → Bool) (i : Fin k) :
    AIG.denote x ⟨(inputsPrefix n k h).1, (inputsPrefix n k h).2 i⟩ = x (i.castLE h) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [inputsPrefix, Fin.snoc_last]
      change AIG.denote x ((inputsPrefix n k (by omega)).1.mkAtom ⟨k, by omega⟩) = _
      rw [AIG.denote_mkAtom]
      rfl
    · simp only [inputsPrefix, Fin.snoc_castSucc]
      rw [AIG.LawfulOperator.denote_cast_entry (f := @AIG.mkAtom (Fin n) _ _)
        (entry := ⟨(inputsPrefix n k (by omega)).1, (inputsPrefix n k (by omega)).2 j⟩)]
      exact ih (by omega) j

def inputs (n : ℕ) := inputsPrefix n n le_rfl

lemma inputs_size (n : ℕ) : (inputs n).1.decls.size = n+1 := inputsPrefix_size ..

lemma inputs_correct (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    AIG.denote x ⟨(inputs n).1, (inputs n).2 i⟩ = x i := inputsPrefix_correct ..

/-- A vector of ordinary references; this constructor emits no graph nodes. -/
def refVector {α : Type} [Hashable α] [DecidableEq α] {g : AIG α} {w : ℕ}
    (f : Fin w → AIG.Ref g) : AIG.RefVec g w where
  refs := Vector.ofFn (fun i => AIG.Fanin.mk (f i).gate (f i).invert)
  hrefs := by intro i hi; simpa using (f ⟨i,hi⟩).hgate

lemma refVector_get {α : Type} [Hashable α] [DecidableEq α] {g : AIG α} {w : ℕ}
    (f : Fin w → AIG.Ref g) (i : ℕ) (hi : i < w) :
    (refVector f).get i hi = f ⟨i,hi⟩ := by
  simp [refVector, AIG.RefVec.get, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]

end ExactQuantumFactoring.AIGCompiler


end

end OAI
