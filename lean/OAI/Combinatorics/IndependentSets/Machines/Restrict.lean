import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.LengthLoop
import OAI.Combinatorics.IndependentSets.Machines.ValuePolynomial

namespace OAI

namespace IndependentSetsCut.CounterMachine

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

end IndependentSetsCut.CounterMachine

end OAI
