import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.Command

namespace OAI

namespace IndependentSetsCut.CounterMachine

section
open Turing
variable {R L : Type} [DecidableEq R]

 theorem advance_simulation (p : L → Instruction R L) (a : Option (Configuration R L)) :
    (a.map embed).bind (TM2.step (fun l => (p l).code)) = (advance p a).map embed := by
  cases a with
  | none => rfl
  | some c => exact step_simulation p c

 theorem iterate_simulation (p : L → Instruction R L) (n : ℕ)
    (a : Option (Configuration R L)) :
    (fun a => a.bind (TM2.step (fun l => (p l).code)))^[n] (a.map embed) =
      ((advance p)^[n] a).map embed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, advance_simulation, Function.iterate_succ_apply']

namespace Command

abbrev FinalLabel (c : Command R) := c.Label ⊕ Unit

def finalCode (c : Command R) : c.FinalLabel → Instruction R c.FinalLabel
  | .inl l => c.code Sum.inl (.inr ()) l
  | .inr _ => .halt

def initial (input : List Bool) : Data R :=
  ⟨fun _ => 0, input, [], []⟩

noncomputable def finiteMachine [Fintype R] (c : Command R) : FinTM2 :=
  machine c.finalCode (.inl c.entry)

 theorem finiteMachine_initial [Fintype R] (c : Command R) (input : List Bool) :
    initList c.finiteMachine input = embed ⟨initial input, some (.inl c.entry)⟩ := by
  unfold initList
  congr 1
  funext k
  cases k <;> simp [finiteMachine, machine, tapes, initial]
  rfl

 noncomputable def machine_run [Fintype R] {c : Command R} {input : List Bool} {out : Data R} {n : ℕ}
    (h : Evaluates c (initial input) out n) :
    StateTransition.EvalsToInTime c.finiteMachine.step (initList c.finiteMachine input)
      (some (embed ⟨out, none⟩)) (n + 1) := by
  have hr := trace h c.finalCode Sum.inl (.inr ()) (fun _ => rfl)
  have hi := iterate_simulation c.finalCode n (atCfg (.inl c.entry) (initial input))
  have hit : (fun a : Option (Configuration R c.FinalLabel) => advance c.finalCode a)^[n + 1]
      (atCfg (.inl c.entry) (initial input)) = some ⟨out, none⟩ := by
    rw [Function.iterate_succ_apply', hr]
    rfl
  refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
  rw [finiteMachine_initial]
  change (fun a => a.bind (TM2.step (fun l => (c.finalCode l).code)))^[n + 1]
      ((atCfg (.inl c.entry) (initial input)).map embed) = _
  rw [iterate_simulation, hit]
  rfl

 theorem finiteMachine_finite_alphabet [Fintype R] (c : Command R)
    (k : c.finiteMachine.K) : Finite (c.finiteMachine.Γ k) := inferInstanceAs (Finite Bool)

end Command
end

open scoped BigOperators
variable {R : Type} [DecidableEq R]

namespace Data

def set (d : Data R) (r : R) (v : ℕ) : Data R :=
  { d with reg := Function.update d.reg r v }

@[simp] theorem set_self (d : Data R) (r : R) : d.set r (d.reg r) = d := by
  simp [set]

@[simp] theorem set_set (d : Data R) (r : R) (v w : ℕ) :
    (d.set r v).set r w = d.set r w := by simp [set]

@[simp] theorem set_reg_same (d : Data R) (r : R) (v : ℕ) :
    (d.set r v).reg r = v := by simp [set]

@[simp] theorem set_reg_ne (d : Data R) (r s : R) (v : ℕ) (h : s ≠ r) :
    (d.set r v).reg s = d.reg s := by simp [set, h]

 theorem set_comm (d : Data R) (r s : R) (v w : ℕ) (h : r ≠ s) :
    (d.set r v).set s w = (d.set s w).set r v := by
  simp only [set]
  congr 1
  exact Function.update_comm h v w d.reg

end Data

namespace Command

def clear (r : R) : Command R := .loop r .skip

def move (r s : R) : Command R := .loop r (.inc s)

 theorem clear_evaluates (d : Data R) (r : R) :
    Evaluates (clear r) d (d.set r 0) (2 * d.reg r + 1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have hs : d.set r 0 = d := by rw [← hn, Data.set_self]
    simpa [clear, hs] using (Evaluates.loop_zero (b := .skip) hn)
  | succ n ih =>
    have hr : d.reg r ≠ 0 := by omega
    have hd : (decData d r).reg r = n := by simp [decData, hn]
    have he := ih (decData d r) hd
    have hf : (decData d r).set r 0 = d.set r 0 := by simp [decData, Data.set]
    have ht : 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1 := by omega
    simpa only [clear, hf, ht] using
      (Evaluates.loop_pos hr (Evaluates.skip (decData d r)) he)

 theorem move_evaluates (d : Data R) (r s : R) (hrs : r ≠ s) :
    Evaluates (move r s) d ((d.set r 0).set s (d.reg s + d.reg r))
      (2 * d.reg r + 1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have hz : d.set r 0 = d := by rw [← hn, Data.set_self]
    simpa [move, hz] using (Evaluates.loop_zero (b := .inc s) hn)
  | succ n ih =>
    have hr : d.reg r ≠ 0 := by omega
    let e := incData (decData d r) s
    have er : e.reg r = n := by simp [e, incData, decData, hrs, hn]
    have es : e.reg s = d.reg s + 1 := by simp [e, incData, decData, Ne.symm hrs]
    have he := ih e er
    have hf : (e.set r 0).set s (e.reg s + n) =
        (d.set r 0).set s (d.reg s + (n + 1)) := by
      simp only [es]
      have hc : e.set r 0 = (d.set r 0).set s (d.reg s + 1) := by
        dsimp [e, incData, decData, Data.set]
        congr 1
        ext t
        by_cases ht : t = r <;> by_cases hs : t = s <;> simp_all
      rw [hc, Data.set_set]
      congr 1
      omega
    have ht : 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1 := by omega
    simpa only [move, hf, ht] using (Evaluates.loop_pos hr (Evaluates.inc (decData d r) s) he)

def Within (c : Command R) (d e : Data R) (B : ℕ) : Prop :=
  ∃ n ≤ B, Evaluates c d e n

 theorem Within.seq {a b : Command R} {d e f : Data R} {B C : ℕ}
    (h : Within a d e B) (h' : Within b e f C) : Within (.seq a b) d f (B + C) := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨m, hm, hf⟩ := h'
  exact ⟨n + m, Nat.add_le_add hn hm, Evaluates.seq he hf⟩

 theorem Within.mono {c : Command R} {d e : Data R} {B C : ℕ}
    (h : Within c d e B) (hBC : B ≤ C) : Within c d e C := by
  obtain ⟨n, hn, he⟩ := h
  exact ⟨n, hn.trans hBC, he⟩

end Command
end IndependentSetsCut.CounterMachine

end OAI
