import Mathlib
import OAI.Computability.MaxCut.Estimates.Put

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset Command

 theorem correct_sum {b f : Expr} (hcb : Correct b) (hcf : Correct f) : Correct (.sum b f) := by
  intro vars k d M hv hc hb hi ha
  let args := fun i => d.reg (vars i)
  let B := b.eval d.input args
  let F := fun i => f.eval d.input (bind args i)
  let V := b.valueBudget M
  let W := f.valueBudget (M+V)
  let T := f.timeBudget (M+V)
  have hB : B ≤ V := b.eval_le d.input args M hi ha
  have hF : ∀ i < B, F i ≤ W := by
    intro i hi'
    apply f.eval_le
    · omega
    · intro j; cases j with
      | zero => dsimp [bind]; omega
      | succ j => exact (ha j).trans (by omega)
  let state : ℕ → Data ℕ := fun i =>
    ((d.set k (∑ j ∈ range (B-i), F j)).set (k+1) i).set (k+2) (B-i)
  have hz : ∀ r, k ≤ r → d.reg r = 0 := hc
  have hbnd := hcb vars (k+1) d M (fun i => by have := hv i; omega)
    (hc.mono (by omega)) hb hi ha
  have hstart : state B = d.set (k+1) B := by
    simp only [state, Nat.sub_self, range_zero, sum_empty]
    rw [Data.set_clean_zero hc le_rfl]
    exact Data.set_clean_zero ((hc.mono (by omega)).set_succ B) le_rfl
  have hloop : Within (.loop (k+1) (.seq (compile (bind vars (k+2)) (k+3) f)
      (.seq (move (k+3) k) (.inc (k+2))))) (state B) (state 0) (B*(T+2*W+3)+1) := by
    apply (Within.loop (k+1) _ state B (T+2*W+2))
    · intro i hi'
      simp [state, Data.set]
    · intro i hi'
      let j := B-(i+1)
      let e := decData (state (i+1)) (k+1)
      have hj : j < B := by dsimp [j]; omega
      have hindex : B-i = j+1 := by dsimp [j]; omega
      have heclean : e.Clean (k+3) := by
        intro r hr
        have h0 : r ≠ k := by omega
        have h1 : r ≠ k+1 := by omega
        have h2 : r ≠ k+2 := by omega
        simp [e, decData, state, Data.set, h0, h1, h2, hc r (by omega)]
      have henv : (fun u => e.reg (bind vars (k+2) u)) = bind args j := by
        funext u
        cases u with
        | zero => simp [e, decData, state, Data.set, bind, j]
        | succ u =>
          have h0 : vars u ≠ k := by have := hv u; omega
          have h1 : vars u ≠ k+1 := by have := hv u; omega
          have h2 : vars u ≠ k+2 := by have := hv u; omega
          simp [e, decData, state, Data.set, bind, args, h0, h1, h2]
      have heargs : ∀ u, e.reg (bind vars (k+2) u) ≤ M+V := by
        intro u
        change (fun u => e.reg (bind vars (k+2) u)) u ≤ M+V
        rw [henv]
        cases u with
        | zero => dsimp [bind]; omega
        | succ u => exact (ha u).trans (by omega)
      have hf := hcf (bind vars (k+2)) (k+3) e (M+V)
        (fun u => by cases u with
          | zero => dsimp [bind]; omega
          | succ u => dsimp [bind]; have := hv u; omega) heclean hb (by exact hi.trans (by omega)) heargs
      rw [henv] at hf
      change Within _ e (e.set (k+3) (F j)) T at hf
      have hm := Within.move (e.set (k+3) (F j)) (k+3) k (by omega)
      let out := (((e.set (k+3) (F j)).set (k+3) 0).set k
        ((e.set (k+3) (F j)).reg k+(e.set (k+3) (F j)).reg (k+3)))
      have hh := hf.seq (hm.seq (Within.inc out (k+2)))
      have hsum : (∑ u ∈ range (B-i), F u) = (∑ u ∈ range j, F u)+F j := by
        rw [hindex, sum_range_succ]
      have hout : incData out (k+2) = state i := by
        apply Data.ext
        · ext u
          have hz3 := hc (k+3) (by omega)
          by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;>
            by_cases h2 : u = k+2 <;> by_cases h3 : u = k+3 <;>
            simp [out, e, state, Data.set, incData, decData,
              h0, h1, h2, h3, j, hsum, hz3] <;> omega
        all_goals rfl
      rw [hout] at hh
      apply hh.mono
      simp only [Data.set_reg_same]
      have := hF j hj
      omega
  rw [hstart] at hloop
  have hclear := Within.clear (state 0) (k+2)
  have hout : (state 0).set (k+2) 0 = d.set k (∑ j ∈ range B, F j) := by
    dsimp only [state]
    rw [Data.set_set]
    apply Data.ext
    · ext u
      have hz1 := hc (k+1) (by omega)
      have hz2 := hc (k+2) (by omega)
      by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;> by_cases h2 : u = k+2 <;>
        simp [Data.set, h0, h1, h2, hz1, hz2]
    all_goals rfl
  rw [hout] at hclear
  have hclear' : Within (clear (k+2)) (state 0) (d.set k (∑ j ∈ range B, F j)) (2*B+1) := by
    simpa [state, Data.set] using hclear
  have hh := hbnd.seq (hloop.seq hclear')
  apply hh.mono

  change _ ≤ b.timeBudget M+V*(T+2*W+3)+2*V+2
  have ht := Nat.mul_le_mul_right (T+2*W+3) hB
  omega

 theorem correct (e : Expr) : Correct e := by
  induction e with
  | const n => exact correct_const n
  | arg i => exact correct_arg i
  | length => exact correct_length
  | bit a ih => exact correct_bit ih
  | add a b ia ib => exact correct_add ia ib
  | sub a b ia ib => exact correct_sub ia ib
  | mul a b ia ib => exact correct_mul ia ib
  | zero a ih => exact correct_zero ih
  | sum b f ib iF => exact correct_sum ib iF

end OptimalMaxCut.CounterMachine.Expr

namespace OptimalMaxCut.CounterMachine

 def Data.restrict (N : ℕ) (d : Data ℕ) : Data (Fin N) :=
  ⟨fun r => d.reg r.val, d.input, d.backup, d.output⟩

namespace Command

 def Bounded (N : ℕ) : Command ℕ → Prop
  | .skip | .write _ | .discard | .rewind => True
  | .inc r | .dec r => r < N
  | .seq a b => Bounded N a ∧ Bounded N b
  | .test r a b => r < N ∧ Bounded N a ∧ Bounded N b
  | .read a b c => Bounded N a ∧ Bounded N b ∧ Bounded N c
  | .loop r b => r < N ∧ Bounded N b

 def regCount : Command ℕ → ℕ
  | .skip | .write _ | .discard | .rewind => 0
  | .inc r | .dec r => r+1
  | .seq a b => max a.regCount b.regCount
  | .test r a b => max (r+1) (max a.regCount b.regCount)
  | .read a b c => max a.regCount (max b.regCount c.regCount)
  | .loop r b => max (r+1) b.regCount

 theorem bounded_of_count (c : Command ℕ) (N : ℕ) (h : c.regCount ≤ N) : c.Bounded N := by
  induction c <;> simp_all [Bounded, regCount]

 def restrict (N : ℕ) : (c : Command ℕ) → Bounded N c → Command (Fin N)
  | .skip, _ => .skip
  | .inc r, h => .inc ⟨r,h⟩
  | .dec r, h => .dec ⟨r,h⟩
  | .write b, _ => .write b
  | .discard, _ => .discard
  | .rewind, _ => .rewind
  | .seq a b, h => .seq (restrict N a h.1) (restrict N b h.2)
  | .test r a b, h => .test ⟨r,h.1⟩ (restrict N a h.2.1) (restrict N b h.2.2)
  | .read a b c, h => .read (restrict N a h.1) (restrict N b h.2.1) (restrict N c h.2.2)
  | .loop r b, h => .loop ⟨r,h.1⟩ (restrict N b h.2)

 theorem restrict_inc (N : ℕ) (d : Data ℕ) (r : ℕ) (h : r<N) :
    (incData d r).restrict N = incData (d.restrict N) ⟨r,h⟩ := by
  apply Data.ext
  · ext u
    simp only [Data.restrict, incData]
    by_cases hu : u.val = r
    · have he : u = ⟨r,h⟩ := Fin.ext hu
      simp [he]
    · have he : u ≠ ⟨r,h⟩ := fun he => hu (congrArg Fin.val he)
      simp [hu, he]
  all_goals rfl

 theorem restrict_dec (N : ℕ) (d : Data ℕ) (r : ℕ) (h : r<N) :
    (decData d r).restrict N = decData (d.restrict N) ⟨r,h⟩ := by
  apply Data.ext
  · ext u
    simp only [Data.restrict, decData]
    by_cases hu : u.val = r
    · have he : u = ⟨r,h⟩ := Fin.ext hu
      simp [he]
    · have he : u ≠ ⟨r,h⟩ := fun he => hu (congrArg Fin.val he)
      simp [hu, he]
  all_goals rfl

 theorem Evaluates.restrict {c : Command ℕ} {d e : Data ℕ} {n : ℕ}
    (he : Evaluates c d e n) (N : ℕ) (h : Bounded N c) :
    Evaluates (c.restrict N h) (d.restrict N) (e.restrict N) n := by
  induction he with
  | skip d => exact Evaluates.skip _
  | inc d r => simpa only [Command.restrict, restrict_inc N d r h] using Evaluates.inc (d.restrict N) ⟨r,h⟩
  | dec d r => simpa only [Command.restrict, restrict_dec N d r h] using Evaluates.dec (d.restrict N) ⟨r,h⟩
  | write d b => exact Evaluates.write _ _
  | discard d => exact Evaluates.discard _
  | rewind_empty hh => exact Evaluates.rewind_empty hh
  | rewind_cons hh he ih => exact Evaluates.rewind_cons hh (ih trivial)
  | seq h1 h2 i1 i2 => exact (i1 h.1).seq (i2 h.2)
  | test_zero hr he ih => exact Evaluates.test_zero hr (ih h.2.1)
  | test_pos hr he ih => exact Evaluates.test_pos hr (ih h.2.2)
  | read_one hr he ih => exact Evaluates.read_one hr (ih h.1)
  | read_zero hr he ih => exact Evaluates.read_zero hr (ih h.2.1)
  | read_empty hr he ih => exact Evaluates.read_empty hr (ih h.2.2)
  | loop_zero hr => exact Evaluates.loop_zero hr
  | @loop_pos r b d e f n m hr h1 h2 i1 i2 =>
    exact Evaluates.loop_pos hr (by simpa only [restrict_dec N d r h.1] using i1 h.2) (i2 h)

 def finite (c : Command ℕ) : Command (Fin c.regCount) :=
  c.restrict c.regCount (c.bounded_of_count _ le_rfl)

 theorem finite_evaluates {c : Command ℕ} {d e : Data ℕ} {n : ℕ}
    (h : Evaluates c d e n) : Evaluates c.finite (d.restrict c.regCount) (e.restrict c.regCount) n :=
  h.restrict _ _

end Command

open scoped BigOperators
open Command

/-- A bit table specified by two bounded-arithmetic expressions. These are
syntax, not assumed computable functions or unit-time arithmetic oracles. -/
def table (len bit : Expr) (input : List Bool) : List Bool :=
  List.ofFn (fun i : Fin (len.eval input (fun _ => 0)) =>
    decide (bit.eval input (fun _ => i.val) ≠ 0))

 def emit (r : ℕ) : Command ℕ := .test r (.write false) (.seq (clear r) (.write true))

 theorem emit_evaluates (d : Data ℕ) (r : ℕ) :
    Within (emit r) d (writeData (d.set r 0) (decide (d.reg r ≠ 0))) (2*d.reg r+3) := by
  by_cases hr : d.reg r = 0
  · refine ⟨2, by omega, ?_⟩
    have h := Evaluates.test_zero (r := r) (b := .seq (clear r) (.write true)) hr
      (Evaluates.write d false)
    have hd : d.set r 0 = d := by rw [← hr, Data.set_self]
    simpa [emit, hr, hd] using h
  · have h := Evaluates.test_pos (a := .write false) hr
      ((clear_evaluates d r).seq (Evaluates.write (d.set r 0) true))
    exact ⟨1+(2*d.reg r+1+1), by omega, by simpa [emit, hr] using h⟩

 def print (len bit : Expr) : Command ℕ :=
  .seq (len.compile (fun _ => 0) 1)
    (.loop 1 (.seq (bit.compile (fun _ => 1) 2) (emit 2)))

 theorem print_evaluates (len bit : Expr) (input : List Bool) :
    Within (print len bit) (initial input)
      {initial input with output := table len bit input}
      (len.timeBudget input.length+len.valueBudget input.length*
        (bit.timeBudget (input.length+len.valueBudget input.length)+
          2*bit.valueBudget (input.length+len.valueBudget input.length)+4)+1) := by
  let d : Data ℕ := initial input
  let L := len.eval input (fun _ => 0)
  let V := len.valueBudget input.length
  let M := input.length+V
  let T := bit.timeBudget M
  let W := bit.valueBudget M
  let out := table len bit input
  have hL : L ≤ V := len.eval_le input _ _ le_rfl (by simp)
  have holen : out.length = L := by simp [out, table, L]
  let state : ℕ → Data ℕ := fun i => {d.set 1 i with output := out.drop i}
  have hlen := len.correct (fun _ => 0) 1 d input.length (by omega)
    (by intro r hr; rfl) rfl le_rfl (by simp [d, initial])
  have hstart : state L = d.set 1 L := by
    simp [state, ← holen, d, initial, Data.set]
  have hloop : Within (.loop 1 (.seq (bit.compile (fun _ => 1) 2) (emit 2)))
      (state L) (state 0) (L*(T+2*W+4)+1) := by
    apply Within.loop 1 _ state L (T+2*W+3)
    · intro i hi; simp [state]
    · intro i hi
      let e := decData (state (i+1)) 1
      have heReg : e.reg = Function.update (fun _ => 0) 1 i := by
        simp [e, state, decData, Data.set, d, initial]
      have heClean : e.Clean 2 := by
        intro r hr
        rw [heReg]
        simp [show r ≠ 1 by omega]
      have heAt : e.reg 1 = i := by simp [heReg]
      have heArg : (fun u : ℕ => e.reg ((fun _ => 1) u)) = (fun _ => i) := by
        funext u; simp [heReg]
      have hc := bit.correct (fun _ => 1) 2 e M (by omega) heClean rfl
        (by change input.length ≤ M; dsimp [M]; omega)
        (by intro u; rw [heAt]; dsimp [M]; omega)
      rw [heArg] at hc
      let B := bit.eval input (fun _ => i)
      change Within _ e (e.set 2 B) T at hc
      have hemit := emit_evaluates (e.set 2 B) 2
      have hd : (e.set 2 B).set 2 0 = e := by
        rw [Data.set_set, Data.set_clean_zero heClean le_rfl]
      simp only [hd, Data.set_reg_same] at hemit
      have hh := hc.seq hemit
      have hdrop : decide (B ≠ 0) :: out.drop (i+1) = out.drop i := by
        have hi' : i < out.length := by omega
        rw [← List.getElem_cons_drop hi']
        congr 1
        simp [out, table, B]
      have hout : writeData e (decide (B ≠ 0)) = state i := by
        apply Data.ext
        · simp [writeData, heReg, state, d, initial, Data.set]
        · rfl
        · rfl
        · exact hdrop
      rw [hout] at hh
      apply hh.mono
      have hB : B ≤ W := bit.eval_le input _ M (by dsimp [M]; omega) (by intro u; dsimp [M]; omega)
      omega
  rw [hstart] at hloop
  have zend : state 0 = {initial input with output := table len bit input} := by
    simp [state, d, Data.set, initial, out]
  rw [zend] at hloop
  exact (hlen.seq hloop).mono (by

    change _ ≤ len.timeBudget input.length+V*(T+2*W+4)+1
    have := Nat.mul_le_mul_right (T+2*W+4) hL
    omega)

/-- Required cleanup before Mathlib's exact halt-list convention. -/
def eraseInput : Command ℕ := .seq (inputLength 1 0) (.loop 0 .discard)

 theorem eraseInput_evaluates (d : Data ℕ) (hz : d.Clean 0) (hb : d.backup = []) :
    Within eraseInput d {d with input := []} (7*d.input.length+7) := by
  have hl := inputLength_evaluates d 1 0 (by omega) (hz 1 (by omega)) (hz 0 le_rfl) hb
  let state : ℕ → Data ℕ := fun i => {d.set 0 i with input := d.input.drop (d.input.length-i)}
  have hs : state d.input.length = d.set 0 d.input.length := by simp [state, Data.set]
  have hf : state 0 = {d with input := []} := by
    simp [state, Data.set_clean_zero hz le_rfl]
  have hloop : Within (.loop 0 .discard) (state d.input.length) (state 0) (2*d.input.length+1) := by
    have h := Within.loop 0 (.discard : Command ℕ) state d.input.length 1
    have heq : 2*d.input.length+1 = d.input.length*(1+1)+1 := by omega
    rw [heq]
    apply h
    · intro i hi; simp [state]
    · intro i hi
      have he : discardData (decData (state (i+1)) 0) = state i := by
        apply Data.ext
        · simp [state, discardData, decData, Data.set]
        · simp only [discardData, decData, state, Data.set]
          rw [List.tail_drop]
          congr 1
          omega
        all_goals rfl
      exact ⟨1,le_rfl, by rw [← he]; exact Evaluates.discard _⟩
  rw [hs, hf] at hloop
  exact (hl.seq hloop).mono (by omega)

end OptimalMaxCut.CounterMachine

end

end OAI
