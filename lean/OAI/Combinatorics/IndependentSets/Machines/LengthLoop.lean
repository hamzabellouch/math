import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.Copy

namespace OAI

namespace IndependentSetsCut.CounterMachine

section
variable {R : Type} [DecidableEq R]
namespace Command

def lengthLoop (guard result : R) : Command R :=
  .loop guard (.read (.seq (.inc guard) (.inc result)) (.seq (.inc guard) (.inc result)) .skip)

 theorem lengthLoop_evaluates (d : Data R) (g r : R) (hgr : g ≠ r) (hg : d.reg g = 1) :
    Within (lengthLoop g r) d
      {((d.set g 0).set r (d.reg r+d.input.length)) with
        input := [], backup := d.input.reverse++d.backup}
      (4*d.input.length+4) := by
  generalize hx : d.input = xs
  induction xs generalizing d with
  | nil =>
    have he : readData (decData d g) = d.set g 0 := by
      simp [readData, decData, Data.set, hx, hg]
    have hread : Evaluates (.read (.seq (.inc g) (.inc r)) (.seq (.inc g) (.inc r)) .skip)
        (decData d g) (d.set g 0) 2 := by
      rw [← he]
      exact Evaluates.read_empty (d := decData d g) hx (Evaluates.skip _)
    have hloop : Evaluates (lengthLoop g r) d (d.set g 0) 4 :=
      Evaluates.loop_pos (by omega) hread (Evaluates.loop_zero (by simp))
    have hf : {((d.set g 0).set r (d.reg r + ([] : List Bool).length)) with input := [], backup := [].reverse++d.backup} = d.set g 0 := by
      apply Data.ext
      · simp [Data.set, Ne.symm hgr]
      · exact hx.symm
      · simp [Data.set]
      · rfl
    exact ⟨4, by simp, by rw [hf]; exact hloop⟩
  | cons b xs ih =>
    let e := incData (incData (readData (decData d g)) g) r
    have eg : e.reg g = 1 := by simp [e, incData, decData, readData, hgr, hg]
    have ei : e.input = xs := by simp [e, incData, decData, readData, hx]
    obtain ⟨n, hn, he⟩ := ih e eg ei
    have hread : Evaluates (.read (.seq (.inc g) (.inc r)) (.seq (.inc g) (.inc r)) .skip)
        (decData d g) e 3 := by
      have hi := Evaluates.seq (Evaluates.inc (readData (decData d g)) g)
        (Evaluates.inc (incData (readData (decData d g)) g) r)
      cases b
      · exact Evaluates.read_zero (d := decData d g) hx hi
      · exact Evaluates.read_one (d := decData d g) hx hi
    have heq : {((e.set g 0).set r (e.reg r+xs.length)) with input := [], backup := xs.reverse++e.backup} =
        {((d.set g 0).set r (d.reg r+(b::xs).length)) with input := [], backup := (b::xs).reverse++d.backup} := by
      apply Data.ext
      · ext u
        by_cases hu : u = g <;> by_cases hr : u = r <;>
          simp [e, incData, decData, readData, Data.set, hu, hr,
            hgr, Ne.symm hgr, hg, Nat.add_assoc, Nat.add_comm]
      · rfl
      · simp [e, incData, decData, readData, hx, List.reverse_cons, List.append_assoc]
      · rfl
    rw [heq] at he
    exact ⟨1+3+n, by simp; omega, Evaluates.loop_pos (by omega) hread he⟩

 def inputLength (g r : R) : Command R := .seq (.inc g) (.seq (lengthLoop g r) .rewind)

 theorem inputLength_evaluates (d : Data R) (g r : R) (hgr : g ≠ r)
    (hg : d.reg g = 0) (hr : d.reg r = 0) (hb : d.backup = []) :
    Within (inputLength g r) d (d.set r d.input.length) (5*d.input.length+6) := by
  have he := lengthLoop_evaluates (incData d g) g r hgr (by simp [incData, hg])
  obtain ⟨n,hn,h⟩ := he
  let e : Data R := {((incData d g).set g 0).set r ((incData d g).reg r+d.input.length)
    with input := [], backup := d.input.reverse++d.backup}
  have he' : Within (lengthLoop g r) (incData d g) e (4*d.input.length+4) := ⟨n,hn,h⟩
  have hw := rewind_evaluates e
  have hout : {e with input := e.backup.reverse++e.input, backup := []} = d.set r d.input.length := by
    apply Data.ext
    · ext u
      by_cases hu : u = g <;> by_cases hu' : u = r <;>
        simp [e, incData, Data.set, hu, hu', hgr, Ne.symm hgr, hg, hr]
    · simp [e, hb, Data.set]
    · exact hb.symm
    · rfl
  have size : e.backup.length = d.input.length := by simp [e, hb]
  have hfull := (Within.inc d g).seq (he'.seq hw)
  rw [hout, size] at hfull
  exact hfull.mono (by omega)

end Command
end

open scoped BigOperators
open Finset

inductive Expr where
  | const (n : ℕ)
  | arg (i : ℕ)
  | length
  | bit (index : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | zero (a : Expr)
  | sum (bound body : Expr)

namespace Expr

def bind (v : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => a
  | n+1 => v n

 def eval (input : List Bool) (args : ℕ → ℕ) : Expr → ℕ
  | .const n => n
  | .arg i => args i
  | .length => input.length
  | .bit e => if (input[eval input args e]?).getD false then 1 else 0
  | .add a b => eval input args a + eval input args b
  | .sub a b => eval input args a - eval input args b
  | .mul a b => eval input args a * eval input args b
  | .zero a => if eval input args a = 0 then 1 else 0
  | .sum b f => ∑ i ∈ range (eval input args b), eval input (bind args i) f

 def valueBudget : Expr → ℕ → ℕ
  | .const n, _ => n
  | .arg _, M => M
  | .length, M => M
  | .bit _, _ => 1
  | .add a b, M => valueBudget a M + valueBudget b M
  | .sub a _, M => valueBudget a M
  | .mul a b, M => valueBudget a M * valueBudget b M
  | .zero _, _ => 1
  | .sum b f, M => valueBudget b M * valueBudget f (M+valueBudget b M)

 theorem eval_le (e : Expr) (input : List Bool) (args : ℕ → ℕ) (M : ℕ)
    (hi : input.length ≤ M) (ha : ∀ i, args i ≤ M) :
    e.eval input args ≤ e.valueBudget M := by
  induction e generalizing args M with
  | const n => exact le_rfl
  | arg i => exact ha i
  | length => exact hi
  | bit e ih => simp only [eval, valueBudget]; split_ifs <;> omega
  | zero e ih => simp only [eval, valueBudget]; split_ifs <;> omega
  | add a b ia ib => exact Nat.add_le_add (ia _ _ hi ha) (ib _ _ hi ha)
  | sub a b ia ib => exact (Nat.sub_le _ _).trans (ia _ _ hi ha)
  | mul a b ia ib => exact Nat.mul_le_mul (ia _ _ hi ha) (ib _ _ hi ha)
  | sum b f ib iF =>
    have hb := ib args M hi ha
    calc
      _ ≤ ∑ _ ∈ range (eval input args b), f.valueBudget (M+b.valueBudget M) := by
        apply sum_le_sum; intro i hi'
        apply iF
        · omega
        · intro j
          cases j with
          | zero => dsimp [bind]; have := mem_range.mp hi'; omega
          | succ j => exact (ha j).trans (by omega)
      _ = eval input args b * f.valueBudget (M+b.valueBudget M) := by simp
      _ ≤ b.valueBudget M * f.valueBudget (M+b.valueBudget M) := Nat.mul_le_mul_right _ hb

 def timeBudget : Expr → ℕ → ℕ
  | .const n, _ => n+1
  | .arg _, M => 5*M+2
  | .length, M => 5*M+6
  | .bit e, M => timeBudget e M+3*valueBudget e M+M+7
  | .add a b, M | .sub a b, M => timeBudget a M+timeBudget b M+2*valueBudget b M+1
  | .mul a b, M => timeBudget a M+timeBudget b M+
      valueBudget b M*(5*valueBudget a M+3)+1+2*valueBudget a M+1+
      2*(valueBudget a M*valueBudget b M)+1
  | .zero a, M => timeBudget a M+2*valueBudget a M+2
  | .sum b f, M => timeBudget b M+valueBudget b M*
      (timeBudget f (M+valueBudget b M)+2*valueBudget f (M+valueBudget b M)+3)+2*valueBudget b M+2

 def compile (vars : ℕ → ℕ) (k : ℕ) : Expr → Command ℕ
  | .const n => Command.put k n
  | .arg i => Command.copy (vars i) k (k+1)
  | .length => Command.inputLength (k+1) k
  | .bit e => .seq (compile vars k e)
      (.seq (Command.inputBit k (k+1)) (Command.move (k+1) k))
  | .add a b => .seq (compile vars k a) (.seq (compile vars (k+1) b) (Command.move (k+1) k))
  | .sub a b => .seq (compile vars k a) (.seq (compile vars (k+1) b) (Command.subFrom (k+1) k))
  | .mul a b => .seq (compile vars k a) (.seq (compile vars (k+1) b)
      (.seq (Command.mulAdd (k+1) k (k+2) (k+3))
        (.seq (Command.clear k) (Command.move (k+2) k))))
  | .zero a => .seq (compile vars k a) (.test k (.inc k) (Command.clear k))
  | .sum b f => .seq (compile vars (k+1) b)
      (.seq (.loop (k+1) (.seq (compile (bind vars (k+2)) (k+3) f)
        (.seq (Command.move (k+3) k) (.inc (k+2))))) (Command.clear (k+2)))

end Expr
namespace Data

def Clean (d : Data ℕ) (k : ℕ) : Prop := ∀ r, k ≤ r → d.reg r = 0

 theorem Clean.mono {d : Data ℕ} {k l : ℕ} (hc : d.Clean k) (h : k ≤ l) : d.Clean l :=
  fun r hr => hc r (h.trans hr)

 theorem Clean.set_succ {d : Data ℕ} {k : ℕ} (hc : d.Clean k) (v : ℕ) :
    (d.set k v).Clean (k+1) := by
  intro r hr
  rw [set_reg_ne _ _ _ _ (by omega)]
  exact hc r (by omega)

 theorem set_args (d : Data ℕ) (vars : ℕ → ℕ) (k v : ℕ) (h : ∀ i, vars i < k) :
    (fun i => (d.set k v).reg (vars i)) = (fun i => d.reg (vars i)) := by
  funext i
  exact set_reg_ne _ _ _ _ (by have := h i; omega)

 theorem set_clean_zero {d : Data ℕ} {k r : ℕ} (hc : d.Clean k) (h : k ≤ r) :
    d.set r 0 = d := by rw [← hc r h, set_self]

end Data
end IndependentSetsCut.CounterMachine

end OAI
