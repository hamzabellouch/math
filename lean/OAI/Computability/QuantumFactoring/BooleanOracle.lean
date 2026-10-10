import Mathlib
import OAI.Computability.QuantumFactoring.BooleanNetworkFurther

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

namespace BoolNet

/-- Only the actual trace, not unrelated output registers, must start at zero. -/
lemma program_eval_range {n k q : ℕ} (p : BoolNet n k) (h : k ≤ q) (x : Basis q)
    (hfresh : ∀ i : Fin q, n ≤ i.val → i.val < k → x i = false) :
    (∀ i : Fin k, (BooleanProgram.eval (p.program h) x) (i.castLE h) =
      p.eval (fun j => x (j.castLE (p.input_le.trans h))) i) ∧
    (∀ i : Fin q, k ≤ i.val → (BooleanProgram.eval (p.program h) x) i = x i) := by
  induction p with
  | input => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  | @add k p o ih =>
    have hk : k ≤ q := by omega
    obtain ⟨hpre, hrest⟩ := ih hk (fun i hi hik => hfresh i hi (by omega))
    have hy : (BooleanProgram.eval (p.program hk) x) ⟨k, by omega⟩ = false := by
      rw [hrest _ (by simp)]
      exact hfresh _ p.input_le (by simp)
    have hv : (o.compileOp h).value (BooleanProgram.eval (p.program hk) x) =
        o.eval (p.eval (fun j => x (j.castLE (p.input_le.trans hk)))) := by
      rw [BoolNode.compileOp_value]
      congr 1
      funext i
      exact hpre i
    have heval : BooleanProgram.eval ((p.add o).program h) x =
        Function.update (BooleanProgram.eval (p.program hk) x) ⟨k, by omega⟩
          (o.eval (p.eval (fun j => x (j.castLE (p.input_le.trans hk))))) := by
      simp only [program, BooleanProgram.eval, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (o.compileOp h).eval (BooleanProgram.eval (p.program hk) x) = _
      rw [BooleanOp.eval_fresh _ _ hy, hv]
      rfl
    rw [heval]
    constructor
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [eval_add_last]
        exact Function.update_self _ _ _
      · rw [eval_add_castSucc]
        rw [Function.update_of_ne (by intro he; have hh := congrArg Fin.val he; change j.val = k at hh; omega)]
        exact hpre j
    · intro i hi
      rw [Function.update_of_ne (by intro he; have hh := congrArg Fin.val he; change i.val = k at hh; omega)]
      exact hrest i (by omega)

end BoolNet

namespace BooleanNetwork

/-- Copy disjoint source wires into a separate target register, by XOR. -/
def copyPrefix {k m : ℕ} (source : Fin m → Fin k) : (t : ℕ) → t ≤ m → BooleanProgram (k+m)
  | 0, _ => []
  | t+1, h => copyPrefix source t (by omega) ++
    [⟨Fin.natAdd k ⟨t, by omega⟩, .copy ((source ⟨t, by omega⟩).castAdd m)
      (by intro he; have hh := congrArg Fin.val he; simp at hh; omega)⟩]

lemma copyPrefix_length {k m : ℕ} (source : Fin m → Fin k) (t : ℕ) (h : t ≤ m) :
    (copyPrefix source t h).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [copyPrefix, ih]

lemma copyPrefix_eval {k m : ℕ} (source : Fin m → Fin k) (t : ℕ) (h : t ≤ m)
    (x : Basis (k+m)) (i : Fin (k+m)) :
    (copyPrefix source t h).eval x i =
      if hi : k ≤ i.val ∧ i.val < k+t then
        Bool.xor (x i) (x ((source ⟨i.val-k, by omega⟩).castAdd m)) else x i := by
  induction t generalizing i with
  | zero => simp [copyPrefix, BooleanProgram.eval]
  | succ t ih =>
    simp only [copyPrefix, BooleanProgram.eval, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (BooleanOp.copy ((source ⟨t, by omega⟩).castAdd m) _).eval
      ((copyPrefix source t (by omega)).eval x) i = _
    by_cases hit : i.val = k+t
    · have he : i = Fin.natAdd k ⟨t, Nat.lt_of_succ_le h⟩ := Fin.ext hit
      subst i
      rw [BooleanOp.eval_at]
      simp only [BooleanOp.value]
      rw [ih, ih]
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      rw [dite_eq_right (by omega), dite_eq_right (by have := (source ⟨t, by omega⟩).isLt; omega),
        dite_eq_left (by omega)]
      simp
    · rw [BooleanOp.eval_away _ _ (by intro he; exact hit (congrArg Fin.val he))]
      rw [ih]
      by_cases hn : k ≤ i.val ∧ i.val < k+t
      · rw [dite_eq_left hn, dite_eq_left (by omega)]
      · rw [dite_eq_right hn, dite_eq_right (by omega)]

/-- Actual fixed-gate compute/copy/uncompute, with all trace wires restored. -/
def oracle {n m : ℕ} (c : BooleanNetwork n m) : List (Instruction (c.width+m)) :=
  let p := c.net.program (Nat.le_add_right c.width m)
  p.compile ++ (copyPrefix c.output m le_rfl).compile ++
    p.compile.reverse.map Instruction.reverse

lemma oracle_length {n m : ℕ} (c : BooleanNetwork n m) :
    c.oracle.length ≤ 4*c.net.count + 2*m := by
  unfold oracle
  simp only [List.length_append, List.length_map, List.length_reverse]
  have hp := c.net.compile_length (Nat.le_add_right c.width m)
  have hc := BooleanProgram.compile_length (copyPrefix c.output m le_rfl)
  rw [copyPrefix_length] at hc
  omega

/-- The basis-state whose trace is zero and whose target is toggled by c(x). -/
def oracleOutput {n m : ℕ} (c : BooleanNetwork n m) (x : Basis (c.width+m)) : Basis (c.width+m) :=
  fun i => if h : c.width ≤ i.val then
    Bool.xor (x i) (c.eval (fun j => x (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _))))
      ⟨i.val-c.width, by omega⟩) else x i

lemma oracle_basis {n m : ℕ} (c : BooleanNetwork n m) (x : Basis (c.width+m))
    (hfresh : ∀ i : Fin (c.width+m), n ≤ i.val → i.val < c.width → x i = false) :
    (programMatrix c.oracle).mulVec (basisVector x) = basisVector (c.oracleOutput x) := by
  let p := c.net.program (Nat.le_add_right c.width m)
  have hx := c.net.program_eval_range (Nat.le_add_right c.width m) x hfresh
  have hout (i : Fin (c.width+m)) (hi : i.val < c.width) : c.oracleOutput x i = x i := by
    simp only [oracleOutput, dite_eq_right (Nat.not_le.mpr hi)]
  have hy := c.net.program_eval_range (Nat.le_add_right c.width m) (c.oracleOutput x)
    (fun i hin hik => (hout i hik).trans (hfresh i hin hik))
  have hin : (fun j : Fin n => c.oracleOutput x
      (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _)))) =
      (fun j => x (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _)))) := by
    funext j
    apply hout
    change j.val < c.width
    exact j.isLt.trans_le c.net.input_le
  rw [hin] at hy
  have he : (copyPrefix c.output m le_rfl).eval (p.eval x) = p.eval (c.oracleOutput x) := by
    funext i
    rw [copyPrefix_eval]
    by_cases hi : c.width ≤ i.val
    · rw [dite_eq_left ⟨hi, i.isLt⟩, hx.2 i hi, hy.2 i hi]
      have hs : p.eval x ((c.output ⟨i.val-c.width, by omega⟩).castAdd m) =
          c.net.eval (fun j => x (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _))))
            (c.output ⟨i.val-c.width, by omega⟩) := hx.1 _
      rw [hs]
      simp only [oracleOutput, dite_eq_left hi, eval, Function.comp_apply]
    · rw [dite_eq_right (by tauto)]
      have hik : i.val < c.width := by omega
      exact (hx.1 ⟨i.val,hik⟩).trans (hy.1 ⟨i.val,hik⟩).symm
  change (programMatrix (p.compile ++ (copyPrefix c.output m le_rfl).compile ++
    p.compile.reverse.map Instruction.reverse)).mulVec (basisVector x) = _
  rw [programMatrix_append, programMatrix_append, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, BooleanProgram.compile_basis, BooleanProgram.compile_basis, he,
    BooleanProgram.uncompute]

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
