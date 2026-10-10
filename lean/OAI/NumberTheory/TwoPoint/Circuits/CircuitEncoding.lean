import OAI.NumberTheory.TwoPoint.Circuits.CircuitComparison
import OAI.NumberTheory.TwoPoint.Circuits.BitEncoding

namespace OAI

/-!
# Truth-table encoding and substitution for residue circuits

Any decoded residue equality is a Boolean function of its block of bits.
Its explicit disjunctive normal form has depth at most two and size at most
`1 + 2^B (1+B)`. Substituting such forms into the actual circuit syntax
increases depth by at most two and multiplies size by this bound.
-/

namespace TwoPointCorrelations.AC0Circuit

open Finset

/-- Replace each positive or negative input literal by a circuit. -/
def substitute {n m : ℕ} (σ : Fin n → Bool → AC0Circuit m) : AC0Circuit n → AC0Circuit m
  | .literal i positive => σ i positive
  | .andGate children => .andGate (fun i => substitute σ (children i))
  | .orGate children => .orGate (fun i => substitute σ (children i))

lemma substitute_eval {n m : ℕ} (σ : Fin n → Bool → AC0Circuit m)
    (F : BooleanCube m → BooleanCube n)
    (hσ : ∀ i positive x, (σ i positive).eval x = if positive then F x i else !(F x i))
    (c : AC0Circuit n) (x : BooleanCube m) : (substitute σ c).eval x = c.eval (F x) := by
  induction c with
  | literal i positive => exact hσ i positive x
  | andGate children ih => simp only [substitute, eval, ih]
  | orGate children ih => simp only [substitute, eval, ih]

lemma substitute_depth {n m d : ℕ} (σ : Fin n → Bool → AC0Circuit m)
    (hσ : ∀ i positive, (σ i positive).depth ≤ d) (c : AC0Circuit n) :
    (substitute σ c).depth ≤ c.depth + d := by
  induction c with
  | literal i positive => simpa [substitute, depth] using hσ i positive
  | andGate children ih =>
      simp only [substitute, depth]
      have hs : (Finset.univ.sup fun i => (substitute σ (children i)).depth) ≤
          (Finset.univ.sup fun i => (children i).depth) + d := by
        apply Finset.sup_le
        intro i hi
        exact (ih i).trans (Nat.add_le_add_right (Finset.le_sup (f := fun i => (children i).depth) hi) d)
      omega
  | orGate children ih =>
      simp only [substitute, depth]
      have hs : (Finset.univ.sup fun i => (substitute σ (children i)).depth) ≤
          (Finset.univ.sup fun i => (children i).depth) + d := by
        apply Finset.sup_le
        intro i hi
        exact (ih i).trans (Nat.add_le_add_right (Finset.le_sup (f := fun i => (children i).depth) hi) d)
      omega

lemma substitute_size {n m K : ℕ} (σ : Fin n → Bool → AC0Circuit m)
    (hK : 1 ≤ K) (hσ : ∀ i positive, (σ i positive).size ≤ K) (c : AC0Circuit n) :
    (substitute σ c).size ≤ K * c.size := by
  induction c with
  | literal i positive => simpa [substitute, size] using hσ i positive
  | andGate children ih =>
      simp only [substitute, size]
      calc
        1 + ∑ i, (substitute σ (children i)).size ≤ K + ∑ i, K * (children i).size :=
          Nat.add_le_add hK (Finset.sum_le_sum (fun i _ => ih i))
        _ = K * (1 + ∑ i, (children i).size) := by rw [← Finset.mul_sum]; ring
  | orGate children ih =>
      simp only [substitute, size]
      calc
        1 + ∑ i, (substitute σ (children i)).size ≤ K + ∑ i, K * (children i).size :=
          Nat.add_le_add hK (Finset.sum_le_sum (fun i _ => ih i))
        _ = K * (1 + ∑ i, (children i).size) := by rw [← Finset.mul_sum]; ring

/-- Conjunction specifying one assignment on a selected block of bits. -/
def assignmentTerm {n B : ℕ} (v : Fin B → Fin n) (z : BooleanCube B) : AC0Circuit n :=
  .andGate (fun i => .literal (v i) (z i))

/-- The constant false circuit, used for rejected rows of a truth table. -/
def falseCircuit (n : ℕ) : AC0Circuit n := .orGate (fun i : Fin 0 => Fin.elim0 i)

lemma literal_eval_true {n : ℕ} (i : Fin n) (positive : Bool) (x : BooleanCube n) :
    (.literal i positive : AC0Circuit n).eval x = true ↔ x i = positive := by
  cases h : x i <;> cases positive <;> simp [eval, h]

lemma assignmentTerm_eval_true {n B : ℕ} (v : Fin B → Fin n)
    (z : BooleanCube B) (x : BooleanCube n) :
    (assignmentTerm v z).eval x = true ↔ (fun i => x (v i)) = z := by
  change (decide (∀ i : Fin B, (.literal (v i) (z i) : AC0Circuit n).eval x = true) = true) ↔ _
  constructor
  · intro h
    funext i
    exact (literal_eval_true (v i) (z i) x).mp ((of_decide_eq_true h) i)
  · intro h
    apply decide_eq_true
    intro i
    exact (literal_eval_true (v i) (z i) x).mpr (congrFun h i)

@[simp] lemma falseCircuit_eval (n : ℕ) (x : BooleanCube n) :
    (falseCircuit n).eval x = false := by simp [falseCircuit, eval]

/-- Explicit DNF with one possible conjunction for each of the `2^B` rows. -/
noncomputable def truthTable {n B : ℕ} (v : Fin B → Fin n)
    (F : BooleanCube B → Bool) : AC0Circuit n :=
  .orGate (fun k : Fin (2 ^ B) =>
    if F (binaryCellEquiv B k) then assignmentTerm v (binaryCellEquiv B k)
    else falseCircuit n)

lemma truthTable_eval {n B : ℕ} (v : Fin B → Fin n) (F : BooleanCube B → Bool)
    (x : BooleanCube n) : (truthTable v F).eval x = F (fun i => x (v i)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [truthTable, eval, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk⟩
    split_ifs at hk with hF
    · have heq := (assignmentTerm_eval_true v (binaryCellEquiv B k) x).mp hk
      rwa [heq]
    · simp only [falseCircuit_eval, Bool.false_eq_true] at hk
  · intro hF
    refine ⟨(binaryCellEquiv B).symm (fun i => x (v i)), ?_⟩
    simp only [Equiv.apply_symm_apply, hF, ite_true]
    exact (assignmentTerm_eval_true v _ x).mpr rfl

lemma assignmentTerm_depth {n B : ℕ} (v : Fin B → Fin n) (z : BooleanCube B) :
    (assignmentTerm v z).depth = 1 := by simp [assignmentTerm, depth]

lemma assignmentTerm_size {n B : ℕ} (v : Fin B → Fin n) (z : BooleanCube B) :
    (assignmentTerm v z).size = 1 + B := by simp [assignmentTerm, size]

lemma truthTable_depth {n B : ℕ} (v : Fin B → Fin n) (F : BooleanCube B → Bool) :
    (truthTable v F).depth ≤ 2 := by
  change 1 + (Finset.univ.sup fun k : Fin (2 ^ B) =>
    (if F (binaryCellEquiv B k) then assignmentTerm v (binaryCellEquiv B k)
      else falseCircuit n).depth) ≤ 2
  have hs : (Finset.univ.sup fun k : Fin (2 ^ B) =>
    (if F (binaryCellEquiv B k) then assignmentTerm v (binaryCellEquiv B k)
      else falseCircuit n).depth) ≤ 1 := by
    apply Finset.sup_le
    intro k _
    split_ifs <;> simp [assignmentTerm_depth, falseCircuit, depth]
  omega

lemma truthTable_size {n B : ℕ} (v : Fin B → Fin n) (F : BooleanCube B → Bool) :
    (truthTable v F).size ≤ 1 + 2 ^ B * (1 + B) := by
  change 1 + (∑ k : Fin (2 ^ B),
    (if F (binaryCellEquiv B k) then assignmentTerm v (binaryCellEquiv B k)
      else falseCircuit n).size) ≤ _
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _k : Fin (2 ^ B), (1 + B) := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs <;> simp [assignmentTerm_size, falseCircuit, size]
    _ = 2 ^ B * (1 + B) := by simp

/-- Encode each residue input using a truth table on its own selected bits. -/
noncomputable def encodeInputs {n m B : ℕ} (v : Fin n → Fin B → Fin m)
    (F : Fin n → BooleanCube B → Bool) (c : AC0Circuit n) : AC0Circuit m :=
  substitute (fun i positive => truthTable (v i)
    (fun z => if positive then F i z else !(F i z))) c

lemma encodeInputs_eval {n m B : ℕ} (v : Fin n → Fin B → Fin m)
    (F : Fin n → BooleanCube B → Bool) (c : AC0Circuit n) (x : BooleanCube m) :
    (encodeInputs v F c).eval x = c.eval (fun i => F i (fun j => x (v i j))) := by
  apply substitute_eval
  intro i positive y
  exact truthTable_eval _ _ y

lemma encodeInputs_depth {n m B : ℕ} (v : Fin n → Fin B → Fin m)
    (F : Fin n → BooleanCube B → Bool) (c : AC0Circuit n) :
    (encodeInputs v F c).depth ≤ c.depth + 2 :=
  substitute_depth _ (fun _ _ => truthTable_depth _ _) c

lemma encodeInputs_size {n m B : ℕ} (v : Fin n → Fin B → Fin m)
    (F : Fin n → BooleanCube B → Bool) (c : AC0Circuit n) :
    (encodeInputs v F c).size ≤ (1 + 2 ^ B * (1 + B)) * c.size :=
  substitute_size _ (by omega) (fun _ _ => truthTable_size _ _) c

end TwoPointCorrelations.AC0Circuit

end OAI
