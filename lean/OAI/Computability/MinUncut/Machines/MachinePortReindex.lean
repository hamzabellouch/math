import Mathlib
import OAI.Computability.MinUncut.Machines.MachineFixedDivMod

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachinePortReindex

open Turing MachineComposition
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) (d : Nat) := MachineFixedDivMod.State A d

def clean (d : Nat) (positive : 0 < d) (ambient : A) : State A d :=
  ((ambient, MachineFixedDivMod.residue d positive 0), none)

inductive Label (d : Nat)
  | copySeed | copyScan | copyRestore | initialize | divide
  | emit (r : Fin d)
  | affineScan | affineRestore | drainQuotient | finish
  deriving DecidableEq, Fintype

def exitAt {divisor : Nat} (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A divisor) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def emit (d : Nat) (positive : 0 < d) (output : K) (b : Nat)
    (r : Fin d) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A d) :=
  pushWord output (List.replicate (r.val + b) true)
    (.load (fun s => clean d positive s.1.1) (.goto fun _ => next))

def instruction (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (Alphabet (K := K)) Λ (State A d)
  | .copySeed => MachineUnaryAffineAt.seed (tape 2) 0 (labels .copyScan)
  | .copyScan => MachineUnaryAffineAt.scan (tape 0) (tape 1) (tape 2) 1
      (labels .copyScan) (labels .copyRestore)
  | .copyRestore => Reduction.MachineTransfer.loopAt (tape 1) (tape 0) id false
      (labels .copyRestore) (some (labels .initialize))
  | .initialize => .push (tape 3) (fun _ => false)
      (.push (tape 4) (fun _ => false) (.goto fun _ => labels .divide))
  | .divide => MachineFixedDivMod.scanLoop d positive (tape 2) (tape 3)
      (labels .divide) (fun r => labels (.emit r))
  | .emit r => emit d positive (tape 4) b r (labels .affineScan)
  | .affineScan => MachineUnaryAffineAt.scan (tape 3) (tape 1) (tape 4) c
      (labels .affineScan) (labels .affineRestore)
  | .affineRestore => Reduction.MachineTransfer.loopAt (tape 1) (tape 3) id false
      (labels .affineRestore) (some (labels .drainQuotient))
  | .drainQuotient => MachineDrain.drain (tape 3) (labels .drainQuotient)
      (some (labels .finish))
  | .finish => .pop (tape 2) (fun s _ => clean d positive s.1.1) (exitAt exit)

def steps (d j : Nat) : Nat := 3 * j + 3 * (j / d) + 11

theorem steps_le (d j : Nat) : steps d j ≤ 6 * j + 11 := by
  have h := Nat.div_le_self j d
  unfold steps
  omega

theorem steps_le_encodedLength (d j : Nat) :
    steps d j ≤ 6 * (encodeWord j).length + 5 := by
  have h := steps_le d j
  rw [encodeWord_length]
  omega

def value (d c b j : Nat) : Nat := c * (j / d) + (j % d) + b

def frame (tape : Fin 5 → K) (base : K → List Bool)
    (work quotient output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes (tape 2) (tape 3) (tape 4) base work quotient output

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem reindexTrace (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = instruction d positive c b tape labels exit l)
    (base : K → List Bool) (j : Nat) (suffix : List Bool)
    (sourceWord : base (tape 0) = encodeWord j ++ suffix)
    (scratchEmpty : base (tape 1) = []) (workEmpty : base (tape 2) = [])
    (quotientEmpty : base (tape 3) = []) (ambient : A) :
    (advance (TM2.step program))^[steps d j]
      (some ⟨some (labels .copySeed), clean d positive ambient, base⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
  have hd (i k : Fin 5) (h : i ≠ k) : tape i ≠ tape k := fun e => h (distinct e)
  let q := j / d
  let r := MachineFixedDivMod.residue d positive j
  let copied := Function.update base (tape 2) (encodeWord j)
  let initialized := frame tape base (encodeWord j) (encodeWord 0)
    (encodeWord 0 ++ base (tape 4))
  let divided := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord 0 ++ base (tape 4))
  let emitted := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord (r.val + b) ++ base (tape 4))
  let computed := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  let drained := frame tape base (encodeWord 0) []
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  have copyRun : (advance (TM2.step program))^[2 * (j + 1) + 1]
      (some ⟨some (labels .copySeed), clean d positive ambient, base⟩) =
      some ⟨some (labels .initialize), clean d positive ambient, copied⟩ := by
    simpa only [clean, copied, Nat.one_mul, Nat.add_zero, workEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 0) (tape 1) (tape 2)
        (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide)) 1 0
        (labels .copySeed) (labels .copyScan) (labels .copyRestore)
        (some (labels .initialize)) program (atLabels .copySeed) (atLabels .copyScan)
        (atLabels .copyRestore) base j suffix sourceWord scratchEmpty
        (ambient, MachineFixedDivMod.residue d positive 0) none
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize), clean d positive ambient, copied⟩) =
      some ⟨some (labels .divide), clean d positive ambient, initialized⟩ := by
    change some (TM2.stepAux (program (labels .initialize)) _ _) = _
    rw [atLabels]
    simp [instruction, TM2.stepAux, copied, initialized, frame, MachineCopy.forkTapes,
      hd 3 2 (by decide), hd 4 2 (by decide), hd 4 3 (by decide), quotientEmpty, encodeWord]
  have divisionInput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base j 0 0 [] [] (base (tape 4)) = initialized := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, initialized, frame]
  have divisionOutput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base 0 q 0 [] [] (base (tape 4)) = divided := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, divided, frame]
  have divideRun : (advance (TM2.step program))^[j + 1]
      (some ⟨some (labels .divide), clean d positive ambient, initialized⟩) =
      some ⟨some (labels (.emit r)), ((ambient, r), some false), divided⟩ := by
    have h := MachineFixedDivMod.scanTrace_fromCount d positive (tape 2) (tape 3) (tape 4)
      (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide))
      (labels .divide) (fun a => labels (.emit a)) program (atLabels .divide)
      base j 0 [] [] (base (tape 4)) ambient none
    simpa only [Nat.zero_div, Nat.zero_add, divisionInput, divisionOutput, clean, r, q] using h
  have emitRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels (.emit r)), ((ambient, r), some false), divided⟩) =
      some ⟨some (labels .affineScan), clean d positive ambient, emitted⟩ := by
    change some (TM2.stepAux (program (labels (.emit r))) _ _) = _
    rw [atLabels]
    simp [instruction, emit, stepAux_pushWord, TM2.stepAux, divided, emitted, frame,
      MachineCopy.forkTapes, List.reverse_replicate, encodeWord, List.append_assoc]
  have affineInput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (r.val + b) ++ base (tape 4)) = emitted := by
    have heq : emitted (tape 3) = encodeWord q := by
      simp [emitted, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
    have hempty : emitted (tape 1) = [] := by
      simp [emitted, frame, MachineCopy.forkTapes, hd 1 2 (by decide),
        hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    have hout : emitted (tape 4) = encodeWord (r.val + b) ++ base (tape 4) := by
      simp [emitted, frame, MachineCopy.forkTapes]
    rw [List.append_nil, ← heq, ← hempty, ← hout]
    exact MachineCopy.forkTapes_self _ _ _ _
  have affineOutput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (c * q + (r.val + b)) ++ base (tape 4)) =
      computed := by
    funext k
    by_cases h1 : k = tape 1
    · subst k
      simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
        hd 1 2 (by decide), hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
          hd 3 1 (by decide), hd 3 4 (by decide)]
      · by_cases h4 : k = tape 4
        · subst k; simp [MachineUnaryAffineAt.tapes, computed, frame, MachineCopy.forkTapes]
        · simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
            h1, h3, h4]
  have affineRun : (advance (TM2.step program))^[2 * (q + 1)]
      (some ⟨some (labels .affineScan), clean d positive ambient, emitted⟩) =
      some ⟨some (labels .drainQuotient), clean d positive ambient, computed⟩ := by
    have h := MachineUnaryAffineAt.affineTrace (tape 3) (tape 1) (tape 4)
      (hd 3 1 (by decide)) (hd 3 4 (by decide)) (hd 1 4 (by decide)) c
      (labels .affineScan) (labels .affineRestore) (some (labels .drainQuotient))
      program (atLabels .affineScan) (atLabels .affineRestore) emitted q (r.val + b)
      [] (base (tape 4)) (ambient, MachineFixedDivMod.residue d positive 0) none
    simpa only [affineInput, affineOutput, clean] using h
  have quotientWord : computed (tape 3) = encodeWord q := by
    simp [computed, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
  have drainOutput : Function.update computed (tape 3) [] = drained := by
    funext k
    by_cases h3 : k = tape 3
    · subst k
      simp [drained, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
    · by_cases h4 : k = tape 4
      · subst k
        simp [computed, drained, frame, MachineCopy.forkTapes, hd 4 3 (by decide)]
      · simp [computed, drained, frame, MachineCopy.forkTapes, h3, h4]
  have drainRun : (advance (TM2.step program))^[q + 2]
      (some ⟨some (labels .drainQuotient), clean d positive ambient, computed⟩) =
      some ⟨some (labels .finish), clean d positive ambient, drained⟩ := by
    have h := MachineDrain.drainTrace (tape 3) (labels .drainQuotient)
      (some (labels .finish)) program (atLabels .drainQuotient)
      computed (computed (tape 3)) (ambient, MachineFixedDivMod.residue d positive 0) none
    rw [Function.update_eq_self, drainOutput, quotientWord, encodeWord_length] at h
    exact h
  have finishOutput : Function.update drained (tape 2) [] =
      Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4)) := by
    have hv : c * q + (r.val + b) = value d c b j := by
      simp [value, q, r, MachineFixedDivMod.residue, Nat.add_assoc]
    funext k
    by_cases h2 : k = tape 2
    · subst k
      simp [hd 2 4 (by decide), workEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [drained, frame, MachineCopy.forkTapes, hd 3 2 (by decide),
          hd 3 4 (by decide), quotientEmpty]
      · by_cases h4 : k = tape 4
        · subst k
          simp [drained, frame, MachineCopy.forkTapes, hd 4 2 (by decide), hv]
        · simp [drained, frame, MachineCopy.forkTapes, h2, h3, h4]
  have finishRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean d positive ambient, drained⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
    have hw : drained (tape 2) = encodeWord 0 := by
      simp [drained, frame, MachineCopy.forkTapes, hd 2 3 (by decide), hd 2 4 (by decide)]
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels]
    cases exit <;> simp [instruction, TM2.stepAux, exitAt, hw, encodeWord, finishOutput, clean]
  have total := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace copyRun initRun) divideRun) emitRun) affineRun) drainRun) finishRun
  have hsteps : steps d j =
      (((((2 * (j + 1) + 1) + 1) + (j + 1)) + 1) + 2 * (q + 1)) + (q + 2) + 1 := by
    dsimp [steps, q]
    omega
  rw [hsteps]
  exact total

def reindexInTime (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = instruction d positive c b tape labels exit l)
    (base : K → List Bool) (j : Nat) (suffix : List Bool)
    (sourceWord : base (tape 0) = encodeWord j ++ suffix)
    (scratchEmpty : base (tape 1) = []) (workEmpty : base (tape 2) = [])
    (quotientEmpty : base (tape 3) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copySeed), clean d positive ambient, base⟩
      (some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩)
      (6 * j + 11) where
  steps := steps d j
  evals_in_steps := reindexTrace d positive c b tape distinct labels exit program atLabels
    base j suffix sourceWord scratchEmpty workEmpty quotientEmpty ambient
  steps_le_m := steps_le d j

def machine (d : Nat) (positive : 0 < d) (c b : Nat) : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label d
  main := .copySeed
  σ := State Unit d
  initialState := clean d positive ()
  m := instruction d positive c b id id none

def machineInTime (d : Nat) (positive : 0 < d) (c b : Nat)
    (base : Fin 5 → List Bool) (j : Nat) (suffix : List Bool)
    (sourceWord : base 0 = encodeWord j ++ suffix)
    (scratchEmpty : base 1 = []) (workEmpty : base 2 = [])
    (quotientEmpty : base 3 = []) :
    StateTransition.EvalsToInTime (machine d positive c b).step
      ⟨some .copySeed, clean d positive (), base⟩
      (some ⟨none, clean d positive (),
        Function.update base (4 : Fin 5) (encodeWord (value d c b j) ++ base 4)⟩)
      (6 * j + 11) :=
  reindexInTime d positive c b id (fun _ _ h => h) id none
    (instruction d positive c b id id none) (fun _ => rfl)
    base j suffix sourceWord scratchEmpty workEmpty quotientEmpty ()

theorem lazy_value (d j : Nat) : value d (2 * d) d j =
    2 * d * (j / d) + d + (j % d) := by
  unfold value
  omega

end MinUncutGames.Foundations.Complexity.MachinePortReindex

end

end OAI
