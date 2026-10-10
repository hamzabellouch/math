import Mathlib
import OAI.Computability.MaxCut.Estimates.Sample

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine
variable {R : Type} [DecidableEq R]
namespace Command

def put (r : R) : ℕ → Command R
  | 0 => .skip
  | n+1 => .seq (.inc r) (put r n)

 theorem put_evaluates (d : Data R) (r : R) (n : ℕ) :
    Within (put r n) d (d.set r (d.reg r+n)) (n+1) := by
  induction n generalizing d with
  | zero => simpa [put] using Within.skip d
  | succ n ih =>
    have h := (Within.inc d r).seq (ih (incData d r))
    have he : (incData d r).set r ((incData d r).reg r+n) = d.set r (d.reg r+(n+1)) := by
      simp [incData, Data.set, Nat.add_assoc, Nat.add_comm]
    rw [he] at h
    simpa only [put, show 1+(n+1) = n+1+1 by omega] using h

 def subFrom (r s : R) : Command R := .loop r (.dec s)

 theorem subFrom_evaluates (d : Data R) (r s : R) (h : r ≠ s) :
    Within (subFrom r s) d ((d.set r 0).set s (d.reg s-d.reg r)) (2*d.reg r+1) := by
  let n := d.reg r
  let state : ℕ → Data R := fun i => (d.set r i).set s (d.reg s-(n-i))
  have hn : state n = d := by simp [state, n]
  have hl : Within (.loop r (.dec s)) (state n) (state 0) (n*2+1) := by
    apply Within.loop r _ state n 1
    · intro i hi; simp [state, Data.set, h]
    · intro i hi
      have he : decData (decData (state (i+1)) r) s = state i := by
        ext u <;> simp only [decData, state, Data.set]
        by_cases hu : u = r <;> by_cases hs : u = s <;>
          simp [hu, hs, h, Ne.symm h] ; omega
      simpa only [he] using Within.dec (decData (state (i+1)) r) s
  simpa [subFrom, state, n, hn, Nat.mul_comm] using hl

 theorem rewind_evaluates (d : Data R) :
    Within (.rewind : Command R) d {d with input := d.backup.reverse++d.input, backup := []}
      (d.backup.length+1) := by
  generalize he : d.backup = xs
  induction xs generalizing d with
  | nil =>
    have hd : {d with input := [].reverse++d.input, backup := []} = d := by
      cases d; simp_all
    exact ⟨1, by simp, by rw [hd]; exact Evaluates.rewind_empty he⟩
  | cons b rest ih =>
    have hb : (backData d).backup = rest := by simp [backData, he]
    obtain ⟨n, hn, h⟩ := ih (backData d) hb
    have hout : {backData d with input := rest.reverse++(backData d).input, backup := []} =
        {d with input := (b::rest).reverse++d.input, backup := []} := by
      simp [backData, he, List.reverse_cons, List.append_assoc]
    rw [hout] at h
    exact ⟨1+n, by simp; omega, Evaluates.rewind_cons he h⟩

/-- Skip exactly the prescribed number of attempted reads, recording only real
bits on the backup. EOF is handled by a genuine branch. -/
def skipInput (r : R) : Command R := .loop r (.read .skip .skip .skip)

 theorem skipInput_evaluates (d : Data R) (r : R) :
    Within (skipInput r) d
      {(d.set r 0) with input := d.input.drop (d.reg r), backup := (d.input.take (d.reg r)).reverse++d.backup}
      (3*d.reg r+1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have he : {d.set r 0 with input := d.input.drop 0, backup := (d.input.take 0).reverse++d.backup} = d := by
      simp only [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append]
      rw [← hn, Data.set_self]
    rw [he]
    exact ⟨1, by omega, Evaluates.loop_zero hn⟩
  | succ n ih =>
    let e := readData (decData d r)
    have he : e.reg r = n := by simp [e, readData, decData, hn]
    obtain ⟨a, ha, hr⟩ := ih e he
    have hb : Evaluates (.read .skip .skip .skip) (decData d r) e 2 := by
      cases hinput : d.input with
      | nil => exact Evaluates.read_empty (d := decData d r) hinput (Evaluates.skip _)
      | cons b rest =>
        cases b
        · exact Evaluates.read_zero (d := decData d r) hinput (Evaluates.skip _)
        · exact Evaluates.read_one (d := decData d r) hinput (Evaluates.skip _)
    have hout : {e.set r 0 with input := e.input.drop n, backup := (e.input.take n).reverse++e.backup} =
        {d.set r 0 with input := d.input.drop (n+1), backup := (d.input.take (n+1)).reverse++d.backup} := by
      cases hi : d.input with
      | nil => simp [e, readData, decData, Data.set, hi]
      | cons b rest => simp [e, readData, decData, Data.set, hi, List.reverse_cons, List.append_assoc]
    rw [hout] at hr
    refine ⟨1+2+a, by omega, Evaluates.loop_pos (by omega) hb hr⟩

/-- Read one bit at a unary index; a missing bit is false. Input is restored. -/
def inputBit (index result : R) : Command R :=
  .seq (skipInput index) (.seq (.read (.inc result) .skip .skip) .rewind)

 theorem inputBit_evaluates (d : Data R) (i r : R) (hir : i ≠ r)
    (hb : d.backup = []) (hr : d.reg r = 0) :
    Within (inputBit i r) d ((d.set i 0).set r (if d.input[d.reg i]?.getD false then 1 else 0))
      (3*d.reg i+d.input.length+4) := by
  let e : Data R := {d.set i 0 with input := d.input.drop (d.reg i), backup := (d.input.take (d.reg i)).reverse++d.backup}
  have he := skipInput_evaluates d i
  let bit := (d.input[d.reg i]?).getD false
  let f : Data R := (readData e).set r (if bit then 1 else 0)
  have hread : Within (.read (.inc r) .skip .skip) e f 2 := by
    have er : e.reg r = 0 := by simp [e, Data.set, Ne.symm hir, hr]
    have bit_head : (e.input.head?).getD false = bit := by
      simp [e, bit, List.head?_drop]
    cases hi : e.input with
    | nil =>
      have hbit : bit = false := by simpa [hi] using bit_head.symm
      have hf : f = readData e := by simp [f, hbit, readData, ← er]
      exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_empty hi (Evaluates.skip _)⟩
    | cons b rest =>
      cases b
      · have hbit : bit = false := by simpa [hi] using bit_head.symm
        have hf : f = readData e := by simp [f, hbit, readData, ← er]
        exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_zero hi (Evaluates.skip _)⟩
      · have hbit : bit = true := by simpa [hi] using bit_head.symm
        have hf : f = incData (readData e) r := by simp [f, hbit, incData, Data.set, readData, er]
        exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_one hi (Evaluates.inc _ _)⟩
  have hrew := rewind_evaluates f
  have restored : {f with input := f.backup.reverse++f.input, backup := []} =
      (d.set i 0).set r (if bit then 1 else 0) := by
    have heq : e.backup.reverse ++ e.input = d.input := by
      simp [e, hb]
    have heq' : (readData e).backup.reverse ++ (readData e).input = d.input := by
      rw [readData]
      simp only [List.reverse_append, List.reverse_take]
      cases hi : e.input <;> simpa [hi, List.append_assoc] using heq
    apply Data.ext
    · rfl
    · exact heq'
    · exact hb.symm
    · rfl
  have size : f.backup.length ≤ d.input.length := by
    dsimp [f, Data.set, readData, e]
    simp only [List.length_append, List.length_take, List.length_reverse, hb, List.length_nil,
      add_zero, List.length_drop]
    omega
  have hh := he.seq (hread.seq hrew)
  rw [restored] at hh
  exact hh.mono (by omega)

end Command
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
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
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
open scoped BigOperators
open Finset

/-- Polynomially bounded arithmetic expressions with finite bounded summation.
The only inspection of the input is by actual bit-read or length macros above.
Bounded sums suffice for divisions, remainder, bounded minimization and every
finite loop in the rounded long-code graph printer. -/
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
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset Command

/-- Exact operational contract: all scratch counters are returned to zero,
original arguments and input are preserved, and a fixed explicit clock holds. -/
def Correct (e : Expr) : Prop := ∀ (vars : ℕ → ℕ) (k : ℕ) (d : Data ℕ) (M : ℕ),
    (∀ i, vars i < k) → d.Clean k → d.backup = [] → d.input.length ≤ M →
    (∀ i, d.reg (vars i) ≤ M) →
    Within (e.compile vars k) d (d.set k (e.eval d.input (fun i => d.reg (vars i)))) (e.timeBudget M)

 theorem correct_const (n : ℕ) : Correct (.const n) := by
  intro vars k d M hv hc hb hi ha
  simpa [compile, eval, timeBudget, hc k le_rfl] using put_evaluates d k n

 theorem correct_arg (i : ℕ) : Correct (.arg i) := by
  intro vars k d M hv hc hb hi ha
  have he := copy_evaluates d (vars i) k (k+1) (by have := hv i; omega)
    (by have := hv i; omega) (by omega) (hc _ (by omega))
  simp only [hc k le_rfl, zero_add] at he
  exact he.mono (by dsimp [timeBudget]; have := ha i; omega)

 theorem correct_length : Correct .length := by
  intro vars k d M hv hc hb hi ha
  exact (inputLength_evaluates d (k+1) k (by omega) (hc _ (by omega)) (hc _ le_rfl) hb).mono
    (by dsimp [timeBudget]; omega)

 theorem binary_start {a b : Expr} (hca : Correct a) (hcb : Correct b)
    (vars : ℕ → ℕ) (k : ℕ) (d : Data ℕ) (M : ℕ)
    (hv : ∀ i, vars i < k) (hc : d.Clean k) (hb : d.backup = []) (hi : d.input.length ≤ M)
    (ha : ∀ i, d.reg (vars i) ≤ M) :
    Within (.seq (a.compile vars k) (b.compile vars (k+1))) d
      ((d.set k (a.eval d.input (fun i => d.reg (vars i)))).set (k+1)
        (b.eval d.input (fun i => d.reg (vars i))))
      (a.timeBudget M+b.timeBudget M) := by
  have h1 := hca vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  have h2 := hcb vars (k+1) (d.set k A) M (fun i => by have := hv i; omega)
    (hc.set_succ A) hb hi (fun i => by
      rw [Data.set_reg_ne d k (vars i) A (Nat.ne_of_lt (hv i))]
      exact ha i)
  rw [Data.set_args d vars k A hv] at h2
  exact h1.seq h2

 theorem correct_add {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.add a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hm := Within.move e (k+1) k (by omega)
  have hout : (e.set (k+1) 0).set k (e.reg k+e.reg (k+1)) = d.set k (A+B) := by
    have hz := hc (k+1) (by omega)
    apply Data.ext
    · ext u
      by_cases hu : u = k <;> by_cases hu' : u = k+1 <;>
        simp [e, Data.set, hu, hu', hz]
    all_goals rfl
  have hm' : Within (move (k+1) k) e (d.set k (A+B)) (2*B+1) := by
    rw [hout] at hm
    simpa only [show e.reg (k+1) = B by simp [e]] using hm
  obtain ⟨s, hsb, hse⟩ := hs
  cases hse with
  | seq h1 h2 =>
    have hh := (show Within _ _ _ _ from ⟨_,le_rfl,h1⟩).seq
      ((show Within _ _ _ _ from ⟨_,le_rfl,h2⟩).seq hm')
    exact hh.mono (by have hB := b.eval_le d.input _ M hi ha; dsimp [timeBudget, B] at *; omega)

 theorem correct_sub {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.sub a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hm := subFrom_evaluates e (k+1) k (by omega)
  have hout : (e.set (k+1) 0).set k (e.reg k-e.reg (k+1)) = d.set k (A-B) := by
    have hz := hc (k+1) (by omega)
    apply Data.ext
    · ext u
      by_cases hu : u = k <;> by_cases hu' : u = k+1 <;>
        simp [e, Data.set, hu, hu', hz]
    all_goals rfl
  have hm' : Within (subFrom (k+1) k) e (d.set k (A-B)) (2*B+1) := by
    rw [hout] at hm
    simpa only [show e.reg (k+1) = B by simp [e]] using hm
  obtain ⟨s, hsb, hse⟩ := hs
  cases hse with
  | seq h1 h2 =>
    have hh := (show Within _ _ _ _ from ⟨_,le_rfl,h1⟩).seq
      ((show Within _ _ _ _ from ⟨_,le_rfl,h2⟩).seq hm')
    exact hh.mono (by have hB := b.eval_le d.input _ M hi ha; dsimp [timeBudget, B] at *; omega)

 theorem correct_zero {a : Expr} (hca : Correct a) : Correct (.zero a) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  have h1 := hca vars k d M hv hc hb hi ha
  have h2 : Within (.test k (.inc k) (clear k)) (d.set k A)
      (d.set k (if A=0 then 1 else 0)) (2*A+2) := by
    by_cases hA : A=0
    · refine ⟨2, by omega, Evaluates.test_zero (r := k) (n := 1) (d := d.set k A) (by simp [hA]) ?_⟩
      simpa [hA, incData, Data.set] using Evaluates.inc (d.set k A) k
    · refine ⟨1+(2*A+1), by omega, Evaluates.test_pos (r := k) (d := d.set k A) (by simpa using hA) ?_⟩
      simpa [hA] using clear_evaluates (d.set k A) k
  have h := h1.seq h2
  exact h.mono (by dsimp [timeBudget]; have := a.eval_le d.input _ M hi ha; dsimp [A] at *; omega)

 theorem correct_bit {a : Expr} (hca : Correct a) : Correct (.bit a) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := if (d.input[A]?).getD false then 1 else 0
  have h1 := hca vars k d M hv hc hb hi ha
  have h2 := inputBit_evaluates (d.set k A) k (k+1) (by omega) hb
    (by rw [Data.set_reg_ne _ _ _ _ (by omega)]; exact hc _ (by omega))
  have hout2 : ((d.set k A).set k 0).set (k+1) B = d.set (k+1) B := by
    rw [Data.set_set, Data.set_clean_zero hc le_rfl]
  simp only [Data.set_reg_same] at h2
  change Within (inputBit k (k+1)) (d.set k A)
    (((d.set k A).set k 0).set (k+1) B) (3*A+d.input.length+4) at h2
  rw [hout2] at h2
  have h3 := Within.move (d.set (k+1) B) (k+1) k (by omega)
  have hout3 : ((d.set (k+1) B).set (k+1) 0).set k
      ((d.set (k+1) B).reg k+(d.set (k+1) B).reg (k+1)) = d.set k B := by
    simp only [Data.set_set]
    rw [Data.set_clean_zero hc (by omega)]
    simp [Data.set, hc k le_rfl]
  have h3' : Within (move (k+1) k) (d.set (k+1) B) (d.set k B) (2*B+1) := by
    rw [hout3] at h3
    simpa only [Data.set_reg_same] using h3
  have h := h1.seq (h2.seq h3')
  have hB : B ≤ 1 := by dsimp [B]; split_ifs <;> omega
  exact h.mono (by have hA := a.eval_le d.input _ M hi ha; dsimp [timeBudget, A] at *; omega)

end OptimalMaxCut.CounterMachine.Expr

namespace OptimalMaxCut.CounterMachine.Command
variable {R : Type} [DecidableEq R]
 theorem Within.assoc {a b c : Command R} {d e : Data R} {B : ℕ}
    (h : Within (.seq (.seq a b) c) d e B) : Within (.seq a (.seq b c)) d e B := by
  obtain ⟨n, hn, he⟩ := h
  cases he with
  | seq hab hc =>
    cases hab with
    | seq ha hb =>
      exact ⟨_, by omega, Evaluates.seq ha (Evaluates.seq hb hc)⟩
end OptimalMaxCut.CounterMachine.Command
namespace OptimalMaxCut.CounterMachine.Expr
open Command

 theorem correct_mul {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.mul a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hz1 := hc (k+1) (by omega)
  have hz2 := hc (k+2) (by omega)
  have hz3 := hc (k+3) (by omega)
  have hm := mulAdd_evaluates e (k+1) k (k+2) (k+3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by simp [e, hz3, Data.set])
  have hout : (e.set (k+1) 0).set (k+2) (e.reg (k+2)+e.reg (k+1)*e.reg k) =
      (d.set k A).set (k+2) (A*B) := by
    apply Data.ext
    · ext u
      by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;> by_cases h2 : u = k+2 <;>
        simp [e, Data.set, h0, h1, h2, hz1, hz2, Nat.mul_comm]
    all_goals rfl
  rw [hout] at hm
  have hm' : Within (mulAdd (k+1) k (k+2) (k+3)) e ((d.set k A).set (k+2) (A*B))
      (B*(5*A+3)+1) := by simpa [e, Data.set] using hm
  let f := (d.set k A).set (k+2) (A*B)
  have hf := Within.clear f k
  have houtf : f.set k 0 = d.set (k+2) (A*B) := by
    change (((d.set k A).set (k+2) (A*B)).set k 0) = _
    rw [Data.set_comm _ k (k+2) _ _ (by omega)]
    rw [Data.set_set]
    rw [Data.set_comm _ (k+2) k _ _ (by omega), Data.set_clean_zero hc le_rfl]
  rw [houtf] at hf
  have hf' : Within (clear k) f (d.set (k+2) (A*B)) (2*A+1) := by
    simpa [f, Data.set] using hf
  have hg := Within.move (d.set (k+2) (A*B)) (k+2) k (by omega)
  have houtg : ((d.set (k+2) (A*B)).set (k+2) 0).set k
      ((d.set (k+2) (A*B)).reg k+(d.set (k+2) (A*B)).reg (k+2)) = d.set k (A*B) := by
    rw [Data.set_set, Data.set_clean_zero hc (by omega)]
    simp [Data.set, hc k le_rfl]
  rw [houtg] at hg
  have hg' : Within (move (k+2) k) (d.set (k+2) (A*B)) (d.set k (A*B)) (2*(A*B)+1) := by
    simpa only [Data.set_reg_same] using hg
  have hh := (hs.seq (hm'.seq (hf'.seq hg'))).assoc
  apply hh.mono
  have hA := a.eval_le d.input _ M hi ha
  have hB := b.eval_le d.input _ M hi ha
  change a.timeBudget M+b.timeBudget M+(B*(5*A+3)+1+(2*A+1+(2*(A*B)+1))) ≤ _
  change A ≤ a.valueBudget M at hA
  change B ≤ b.valueBudget M at hB
  dsimp only [timeBudget]
  calc
    _ ≤ a.timeBudget M+b.timeBudget M+
        (b.valueBudget M*(5*a.valueBudget M+3)+1+
          (2*a.valueBudget M+1+(2*(a.valueBudget M*b.valueBudget M)+1))) := by gcongr
    _ = _ := by omega

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
