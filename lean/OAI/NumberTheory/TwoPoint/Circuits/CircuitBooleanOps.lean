import OAI.NumberTheory.TwoPoint.Circuits.CircuitEncoding

namespace OAI

/-! Relabel, complement and conjoin the residue circuits used in a
closed-word expansion without increasing their internal depth. -/

namespace TwoPointCorrelations.AC0Circuit

open Finset

def negate {n : ℕ} : AC0Circuit n → AC0Circuit n
  | .literal i b => .literal i (!b)
  | .andGate c => .orGate (fun i => negate (c i))
  | .orGate c => .andGate (fun i => negate (c i))

lemma negate_eval {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) :
    c.negate.eval x = true ↔ c.eval x ≠ true := by
  induction c with
  | literal i b => cases b <;> cases hx : x i <;> simp [negate, eval, hx]
  | andGate c ih => simp only [negate, eval, ne_eq, decide_eq_true_eq, ih, not_forall]
  | orGate c ih => simp only [negate, eval, ne_eq, decide_eq_true_eq, ih, not_exists]

lemma negate_depth {n : ℕ} (c : AC0Circuit n) : c.negate.depth = c.depth := by
  induction c with
  | literal i b => rfl
  | andGate c ih => simp only [negate, depth, ih]
  | orGate c ih => simp only [negate, depth, ih]

lemma negate_size {n : ℕ} (c : AC0Circuit n) : c.negate.size = c.size := by
  induction c with
  | literal i b => rfl
  | andGate c ih => simp only [negate, size, ih]
  | orGate c ih => simp only [negate, size, ih]

def relabel {n m : ℕ} (f : Fin n → Fin m) (c : AC0Circuit n) : AC0Circuit m :=
  substitute (fun i b => .literal (f i) b) c

lemma relabel_eval {n m : ℕ} (f : Fin n → Fin m) (c : AC0Circuit n) (x : BooleanCube m) :
    (relabel f c).eval x = c.eval (fun i => x (f i)) :=
  substitute_eval _ (fun x i => x (f i)) (fun _ _ _ => rfl) c x

lemma relabel_depth {n m : ℕ} (f : Fin n → Fin m) (c : AC0Circuit n) :
    (relabel f c).depth ≤ c.depth := by
  simpa only [relabel, Nat.add_zero] using substitute_depth (fun i b => literal (f i) b)
    (d := 0) (fun _ _ => Nat.le_refl 0) c

lemma relabel_size {n m : ℕ} (f : Fin n → Fin m) (c : AC0Circuit n) :
    (relabel f c).size ≤ c.size := by
  simpa only [relabel, Nat.one_mul] using substitute_size (fun i b => literal (f i) b)
    (K := 1) (by omega) (fun _ _ => Nat.le_refl 1) c

noncomputable def conjunction {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : AC0Circuit n :=
  .andGate (fun i : Fin (Fintype.card ι) => c ((Fintype.equivFin ι).symm i))

lemma conjunction_eval {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) (x : BooleanCube n) :
    (conjunction c).eval x = true ↔ ∀ i, (c i).eval x = true := by
  simp only [conjunction, eval, decide_eq_true_eq]
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h ((Fintype.equivFin ι) i)
  · intro h i
    exact h _

lemma conjunction_depth {ι : Type*} [Fintype ι] {n d : ℕ}
    (c : ι → AC0Circuit n) (hc : ∀ i, (c i).depth ≤ d) :
    (conjunction c).depth ≤ d + 1 := by
  simp only [conjunction, depth]
  have hh : (univ.sup fun i : Fin (Fintype.card ι) =>
      (c ((Fintype.equivFin ι).symm i)).depth) ≤ d :=
    Finset.sup_le (fun i _ => hc _)
  omega

lemma conjunction_size {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : (conjunction c).size = 1 + ∑ i, (c i).size := by
  simp only [conjunction, size]
  congr 1
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => (c i).size)

end TwoPointCorrelations.AC0Circuit

end OAI
