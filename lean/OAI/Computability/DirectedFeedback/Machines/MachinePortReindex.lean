import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.ExpanderTableWords

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachinePortReindex

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

def exitAt {d : Nat} (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A d) :=
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

private def frame_inline_MachinePortReindex (tape : Fin 5 → K) (base : K → List Bool)
    (work quotient output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes (tape 2) (tape 3) (tape 4) base work quotient output

private theorem joinTrace_inline_MachinePortReindex {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
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
  let initialized := frame_inline_MachinePortReindex tape base (encodeWord j) (encodeWord 0)
    (encodeWord 0 ++ base (tape 4))
  let divided := frame_inline_MachinePortReindex tape base (encodeWord 0) (encodeWord q)
    (encodeWord 0 ++ base (tape 4))
  let emitted := frame_inline_MachinePortReindex tape base (encodeWord 0) (encodeWord q)
    (encodeWord (r.val + b) ++ base (tape 4))
  let computed := frame_inline_MachinePortReindex tape base (encodeWord 0) (encodeWord q)
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  let drained := frame_inline_MachinePortReindex tape base (encodeWord 0) []
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
    simp [instruction, TM2.stepAux, copied, initialized, frame_inline_MachinePortReindex, MachineCopy.forkTapes,
      hd 3 2 (by decide), hd 4 2 (by decide), hd 4 3 (by decide), quotientEmpty, encodeWord]
  have divisionInput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base j 0 0 [] [] (base (tape 4)) = initialized := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, initialized, frame_inline_MachinePortReindex]
  have divisionOutput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base 0 q 0 [] [] (base (tape 4)) = divided := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, divided, frame_inline_MachinePortReindex]
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
    simp [instruction, emit, stepAux_pushWord, TM2.stepAux, divided, emitted, frame_inline_MachinePortReindex,
      MachineCopy.forkTapes, List.reverse_replicate, encodeWord, List.append_assoc]
  have affineInput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (r.val + b) ++ base (tape 4)) = emitted := by
    have heq : emitted (tape 3) = encodeWord q := by
      simp [emitted, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 3 4 (by decide)]
    have hempty : emitted (tape 1) = [] := by
      simp [emitted, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 1 2 (by decide),
        hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    have hout : emitted (tape 4) = encodeWord (r.val + b) ++ base (tape 4) := by
      simp [emitted, frame_inline_MachinePortReindex, MachineCopy.forkTapes]
    rw [List.append_nil, ← heq, ← hempty, ← hout]
    exact MachineCopy.forkTapes_self _ _ _ _
  have affineOutput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (c * q + (r.val + b)) ++ base (tape 4)) =
      computed := by
    funext k
    by_cases h1 : k = tape 1
    · subst k
      simp [MachineUnaryAffineAt.tapes, emitted, computed, frame_inline_MachinePortReindex, MachineCopy.forkTapes,
        hd 1 2 (by decide), hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [MachineUnaryAffineAt.tapes, emitted, computed, frame_inline_MachinePortReindex, MachineCopy.forkTapes,
          hd 3 1 (by decide), hd 3 4 (by decide)]
      · by_cases h4 : k = tape 4
        · subst k; simp [MachineUnaryAffineAt.tapes, computed, frame_inline_MachinePortReindex, MachineCopy.forkTapes]
        · simp [MachineUnaryAffineAt.tapes, emitted, computed, frame_inline_MachinePortReindex, MachineCopy.forkTapes,
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
    simp [computed, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 3 4 (by decide)]
  have drainOutput : Function.update computed (tape 3) [] = drained := by
    funext k
    by_cases h3 : k = tape 3
    · subst k
      simp [drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 3 4 (by decide)]
    · by_cases h4 : k = tape 4
      · subst k
        simp [computed, drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 4 3 (by decide)]
      · simp [computed, drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, h3, h4]
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
        simp [drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 3 2 (by decide),
          hd 3 4 (by decide), quotientEmpty]
      · by_cases h4 : k = tape 4
        · subst k
          simp [drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 4 2 (by decide), hv]
        · simp [drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, h2, h3, h4]
  have finishRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean d positive ambient, drained⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
    have hw : drained (tape 2) = encodeWord 0 := by
      simp [drained, frame_inline_MachinePortReindex, MachineCopy.forkTapes, hd 2 3 (by decide), hd 2 4 (by decide)]
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels]
    cases exit <;> simp [instruction, TM2.stepAux, exitAt, hw, encodeWord, finishOutput, clean]
  have total := joinTrace_inline_MachinePortReindex (joinTrace_inline_MachinePortReindex (joinTrace_inline_MachinePortReindex (joinTrace_inline_MachinePortReindex (joinTrace_inline_MachinePortReindex
    (joinTrace_inline_MachinePortReindex copyRun initRun) divideRun) emitRun) affineRun) drainRun) finishRun
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

end DFVSGames.Foundations.Complexity.MachinePortReindex

end

section

namespace DFVSGames.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open DFVSGames.Foundations.Complexity

variable {n d : Nat}

def row (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    DartRow n (n * d) :=
  ⟨v, table.reverseIndex[rowIndex n d (v, p)], table.relations[rowIndex n d (v, p)]⟩

def trueRelation : RelationTable := Vector.replicate 4096 true

def stayRow (d : Nat) (v : Fin n) (p : Fin d) : DartRow n (n * (2 * d)) :=
  ⟨v, rowIndex n (2 * d) (v, lazyPorts d (false, p)), trueRelation⟩

def moveRow (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    DartRow n (n * (2 * d)) :=
  ⟨v, rowIndex n (2 * d) ((rotation table (v, p)).1,
    lazyPorts d (true, (rotation table (v, p)).2)),
    table.relations[rowIndex n d (v, p)]⟩

def reverseMap (d j : Nat) : Nat := 2 * d * (j / d) + d + j % d

private theorem relation_ext_inline_PreprocessingLazyWords {r s : RelationTable}
    (h : ∀ a b, relationAt r a b = relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [relationAt, Prod.eta, Equiv.apply_symm_apply, Fin.getElem_fin] using
    h (relationIndex.symm ⟨i, hi⟩).1 (relationIndex.symm ⟨i, hi⟩).2

theorem row_lazy_stay (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (false, p)) = stayRow d v p := by
  have hr : (lazy table).reverseIndex[rowIndex n (2 * d) (v, lazyPorts d (false, p))] =
      rowIndex n (2 * d) (v, lazyPorts d (false, p)) := by
    rw [← rowIndex_rotation, lazy_rotation_false]
  have hp : (lazy table).relations[rowIndex n (2 * d) (v, lazyPorts d (false, p))] =
      trueRelation := by
    apply relation_ext_inline_PreprocessingLazyWords
    intro a b
    simpa only [PortTables.accepts, relationAt, trueRelation, Fin.getElem_fin,
      Vector.getElem_replicate] using lazy_accepts_false table v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem row_lazy_move (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (true, p)) = moveRow table v p := by
  have hr : (lazy table).reverseIndex[rowIndex n (2 * d) (v, lazyPorts d (true, p))] =
      rowIndex n (2 * d) ((rotation table (v, p)).1,
        lazyPorts d (true, (rotation table (v, p)).2)) := by
    rw [← rowIndex_rotation, lazy_rotation_true]
  have hp : (lazy table).relations[rowIndex n (2 * d) (v, lazyPorts d (true, p))] =
      table.relations[rowIndex n d (v, p)] := by
    apply relation_ext_inline_PreprocessingLazyWords
    intro a b
    exact lazy_accepts_true table v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem stayRow_reverse_val (v : Fin n) (p : Fin d) :
    (stayRow d v p).reverseIndex.val = 2 * d * v.val + p.val := by
  simp only [stayRow, rowIndex_val, lazyPorts_false_val]
  omega

theorem moveRow_reverse_val (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    (moveRow table v p).reverseIndex.val =
      reverseMap d (row table v p).reverseIndex.val := by
  simp only [moveRow, rowIndex_val, lazyPorts_true_val, reverseMap, row]
  change (table.reverseIndex[rowIndex n d (v, p)]).val % d + d +
      (2 * d) * ((table.reverseIndex[rowIndex n d (v, p)]).val / d) = _
  omega

theorem relationWords_true : relationWords trueRelation = List.replicate 4096 1 := by
  simp only [relationWords, trueRelation, Vector.toList_replicate,
    List.map_replicate, bitWord, ite_true]

theorem stayRow_words (v : Fin n) (p : Fin d) :
    rowWords (stayRow d v p) =
      [v.val, 2 * d * v.val + p.val] ++ List.replicate 4096 1 := by
  rw [rowWords, stayRow_reverse_val]
  exact congrArg (fun words => [v.val, 2 * d * v.val + p.val] ++ words) relationWords_true

theorem moveRow_words (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    rowWords (moveRow table v p) =
      [v.val, reverseMap d (row table v p).reverseIndex.val] ++
        relationWords (row table v p).relation := by
  rw [rowWords, moveRow_reverse_val]
  rfl

theorem ofFn_rowIndex {α : Type*} (f : Fin (n * d) → α) :
    List.ofFn f = (List.ofFn fun v : Fin n =>
      List.ofFn fun p : Fin d => f (rowIndex n d (v, p))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  congr 1
  funext v
  congr 1
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val]
  ac_rfl

theorem flatRows_list (table : PortTables.Table n d) :
    (flatRows table).toList =
      (List.ofFn fun v : Fin n => List.ofFn (row table v)).flatten := by
  rw [flatRows, Vector.toList_ofFn, ofFn_rowIndex]
  simp only [Equiv.symm_apply_apply]
  rfl

theorem ofFn_lazyPorts {α : Type*} (f : Fin (2 * d) → α) :
    List.ofFn f = List.ofFn (fun p => f (lazyPorts d (false, p))) ++
      List.ofFn (fun p => f (lazyPorts d (true, p))) := by
  have hf (p : Fin d) : rowIndex 2 d (0, p) = lazyPorts d (false, p) := by
    apply Fin.ext
    simp only [rowIndex_val, Fin.val_zero, Nat.mul_zero, Nat.add_zero, lazyPorts_false_val]
  have ht (p : Fin d) : rowIndex 2 d ((0 : Fin 1).succ, p) = lazyPorts d (true, p) := by
    apply Fin.ext
    simp only [rowIndex_val, Fin.val_succ, Fin.val_zero, Nat.zero_add,
      Nat.mul_one, lazyPorts_true_val]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, hf, ht] using (ofFn_rowIndex (n := 2) (d := d) f)

def vertexRows (table : PortTables.Table n d) (v : Fin n) :
    List (DartRow n (n * (2 * d))) :=
  List.ofFn (stayRow d v) ++ List.ofFn (moveRow table v)

theorem vertexRows_length (table : PortTables.Table n d) (v : Fin n) :
    (vertexRows table v).length = 2 * d := by
  simp only [vertexRows, List.length_append, List.length_ofFn]
  omega

theorem flatRows_lazy (table : PortTables.Table n d) :
    (flatRows (lazy table)).toList = (List.ofFn (vertexRows table)).flatten := by
  rw [flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_lazyPorts]
  simp only [row_lazy_stay, row_lazy_move]
  rfl

theorem vertexRows_words (table : PortTables.Table n d) (v : Fin n) :
    (vertexRows table v).flatMap rowWords =
      (List.ofFn fun p : Fin d =>
        [v.val, 2 * d * v.val + p.val] ++ List.replicate 4096 1).flatten ++
      (List.ofFn fun p : Fin d =>
        [v.val, reverseMap d (row table v p).reverseIndex.val] ++
          relationWords (row table v p).relation).flatten := by
  have hs : rowWords ∘ stayRow d v = fun p : Fin d =>
      [v.val, 2 * d * v.val + p.val] ++ List.replicate 4096 1 := by
    funext p
    exact stayRow_words v p
  have hm : rowWords ∘ moveRow table v = fun p : Fin d =>
      [v.val, reverseMap d (row table v p).reverseIndex.val] ++
        relationWords (row table v p).relation := by
    funext p
    exact moveRow_words table v p
  simp only [vertexRows, List.flatMap_def, List.map_append, List.map_ofFn,
    List.flatten_append]
  rw [hs, hm]

theorem tableWords_lazy (table : PortTables.Table n d) :
    PortTables.tableWords (lazy table) =
      [n, n * (2 * d)] ++ (List.ofFn (vertexRows table)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_lazy]

theorem tableBits_lazy (table : PortTables.Table n d) :
    PortTables.tableBits (lazy table) =
      encodeWords ([n, n * (2 * d)] ++
        (List.ofFn (vertexRows table)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (lazy table)) = _
  rw [tableWords_lazy]

end DFVSGames.Foundations.PCP.PreprocessingLazyWords
end

section

namespace DFVSGames.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

abbrev Label (d : Nat) := MachinePortReindex.Label d ⊕ MachineTableRows.Label
abbrev State (A : Type) (d : Nat) := MachinePortReindex.State A d

def addressIndex : Fin 5 → Fin 9 := ![1, 3, 4, 5, 6]

theorem addressIndex_injective : Function.Injective addressIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [addressIndex]

def fields (tape : Fin 9 → K) : Fin 3 → K := ![tape 0, tape 6, tape 2]

def reindexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State A d)
  | .inl stage => MachinePortReindex.instruction d positive c b
      (tape ∘ addressIndex) (fun stage => labels (.inl stage))
      (some (labels (.inr .relationRead))) stage
  | .inr stage => MachineTableRows.routine (fields tape) (tape 8) (tape 7) (tape 3)
      (fun stage => labels (.inr stage)) exit stage

def instruction (d : Nat) (positive : 0 < d) (tape : Fin 9 → K)
    (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State A d) :=
  reindexInstruction d positive (2 * d) d tape labels exit

def reindexRowBits (d c b v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord (MachinePortReindex.value d c b j) ++
    encodeWords (relationWords relation)

def reindexMappedTapes (d c b j : Nat) (tape : Fin 9 → K)
    (base : K → List Bool) : K → List Bool :=
  Function.update base (tape 6) (encodeWord (MachinePortReindex.value d c b j))

def reindexResultTapes (d c b v j : Nat) (relation : RelationTable)
    (tape : Fin 9 → K) (base : K → List Bool) : K → List Bool :=
  Function.update (reindexMappedTapes d c b j tape base) (tape 7)
    (base (tape 7) ++ reindexRowBits d c b v j relation)

def reindexSteps (d c b v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  MachinePortReindex.steps d j + 4 * (reindexRowBits d c b v j relation).length +
    2 * output.length + 9

def rowBits (d v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord (reverseMap d j) ++ encodeWords (relationWords relation)

def mappedTapes (d j : Nat) (tape : Fin 9 → K) (base : K → List Bool) : K → List Bool :=
  Function.update base (tape 6) (encodeWord (reverseMap d j))

def resultTapes (d v j : Nat) (relation : RelationTable)
    (tape : Fin 9 → K) (base : K → List Bool) : K → List Bool :=
  Function.update (mappedTapes d j tape base) (tape 7)
    (base (tape 7) ++ rowBits d v j relation)

def steps (d v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  MachinePortReindex.steps d j + 4 * (rowBits d v j relation).length + 2 * output.length + 9

theorem reindexRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (distinct : Function.Injective tape) (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = reindexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable)
    (tailWord : base (tape 0) = encodeWord v)
    (reverseWord : base (tape 1) = encodeWord j)
    (relationWord : base (tape 2) = encodeWords (relationWords relation))
    (scratchEmpty : base (tape 3) = []) (workEmpty : base (tape 4) = [])
    (quotientEmpty : base (tape 5) = []) (newReverseEmpty : base (tape 6) = [])
    (rowEmpty : base (tape 8) = []) (ambient : A) :
    (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean d positive ambient,
        reindexResultTapes d c b v j relation tape base⟩ := by
  have hd (i k : Fin 9) (h : i ≠ k) : tape i ≠ tape k := fun e => h (distinct e)
  have ha0 : addressIndex 0 = 1 := rfl
  have ha4 : addressIndex 4 = 6 := rfl
  have mapRun := MachinePortReindex.reindexTrace d positive c b
    (tape ∘ addressIndex) (distinct.comp addressIndex_injective)
    (fun stage => labels (.inl stage)) (some (labels (.inr .relationRead)))
    program (fun stage => atLabels (.inl stage)) base j []
    (by simpa only [Function.comp_apply, ha0, List.append_nil] using reverseWord)
    scratchEmpty workEmpty quotientEmpty ambient
  simp only [Function.comp_apply, ha4, newReverseEmpty,
    List.append_nil] at mapRun
  change (advance (TM2.step program))^[MachinePortReindex.steps d j]
    (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
    some ⟨some (labels (.inr .relationRead)), MachinePortReindex.clean d positive ambient,
      reindexMappedTapes d c b j tape base⟩ at mapRun
  have hfields (i : Fin 3) : fields tape i ≠ tape 8 ∧ fields tape i ≠ tape 3 := by
    fin_cases i
    · exact ⟨hd 0 8 (by decide), hd 0 3 (by decide)⟩
    · exact ⟨hd 6 8 (by decide), hd 6 3 (by decide)⟩
    · exact ⟨hd 2 8 (by decide), hd 2 3 (by decide)⟩
  have hbits : MachineTableRows.fieldBits (fields tape) (reindexMappedTapes d c b j tape base) =
      reindexRowBits d c b v j relation := by
    simp [MachineTableRows.fieldBits, fields, reindexMappedTapes, hd 0 6 (by decide),
      hd 2 6 (by decide), tailWord, relationWord, reindexRowBits]
  have hsize : MachineTableRows.fieldSize (fields tape) (reindexMappedTapes d c b j tape base) =
      (reindexRowBits d c b v j relation).length := by
    rw [← MachineTableRows.fieldBits_length, hbits]
  have hout : reindexMappedTapes d c b j tape base (tape 7) = base (tape 7) := by
    simp [reindexMappedTapes, hd 7 6 (by decide)]
  have appendRun := MachineTableRows.appendTrace (fields tape) (tape 8) (tape 7) (tape 3)
    hfields (hd 8 7 (by decide)) (hd 8 3 (by decide)) (hd 7 3 (by decide))
    (fun stage => labels (.inr stage)) exit program
    (fun stage => atLabels (.inr stage)) (reindexMappedTapes d c b j tape base)
    (by simp [reindexMappedTapes, hd 8 6 (by decide), rowEmpty])
    (by simp [reindexMappedTapes, hd 3 6 (by decide), scratchEmpty])
    (ambient, MachineFixedDivMod.residue d positive 0) none
  rw [hsize, hout, hbits] at appendRun
  change (advance (TM2.step program))^[4 * (reindexRowBits d c b v j relation).length +
      2 * (base (tape 7)).length + 9]
    (some ⟨some (labels (.inr .relationRead)), MachinePortReindex.clean d positive ambient,
      reindexMappedTapes d c b j tape base⟩) =
    some ⟨exit, MachinePortReindex.clean d positive ambient,
      reindexResultTapes d c b v j relation tape base⟩ at appendRun
  rw [show reindexSteps d c b v j relation (base (tape 7)) =
      (4 * (reindexRowBits d c b v j relation).length + 2 * (base (tape 7)).length + 9) +
        MachinePortReindex.steps d j by unfold reindexSteps; omega,
    Function.iterate_add_apply, mapRun, appendRun]

theorem rowTrace (d : Nat) (positive : 0 < d) (tape : Fin 9 → K)
    (distinct : Function.Injective tape) (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = instruction d positive tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable)
    (tailWord : base (tape 0) = encodeWord v)
    (reverseWord : base (tape 1) = encodeWord j)
    (relationWord : base (tape 2) = encodeWords (relationWords relation))
    (scratchEmpty : base (tape 3) = []) (workEmpty : base (tape 4) = [])
    (quotientEmpty : base (tape 5) = []) (newReverseEmpty : base (tape 6) = [])
    (rowEmpty : base (tape 8) = []) (ambient : A) :
    (advance (TM2.step program))^[steps d v j relation (base (tape 7))]
      (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean d positive ambient,
        resultTapes d v j relation tape base⟩ := by
  simpa only [reindexSteps, reindexResultTapes, reindexMappedTapes, reindexRowBits,
    MachinePortReindex.lazy_value, reverseMap, steps, resultTapes, mappedTapes, rowBits] using
    reindexRowTrace d positive (2 * d) d tape distinct labels exit program atLabels
      base v j relation tailWord reverseWord relationWord scratchEmpty workEmpty
      quotientEmpty newReverseEmpty rowEmpty ambient

theorem rowBits_eq_moveRow {n d : Nat} (table : PCP.PortTables.Table n d)
    (v : Fin n) (p : Fin d) :
    rowBits d v.val (PCP.PreprocessingLazyWords.row table v p).reverseIndex.val
        (PCP.PreprocessingLazyWords.row table v p).relation =
      encodeWords (rowWords (moveRow table v p)) := by
  rw [moveRow_words]
  simp [rowBits, encodeWords]

def machine (d : Nat) (positive : 0 < d) : FinTM2 where
  K := Fin 9
  k₀ := 1
  k₁ := 7
  Γ _ := Bool
  Λ := Label d
  main := .inl .copySeed
  σ := State Unit d
  initialState := MachinePortReindex.clean d positive ()
  m := instruction d positive id id none

abbrev Buffer := MachineRegularOriginalRow.Buffer
abbrev StreamState (A : Type) (d : Nat) := State (A × Buffer) d

def streamClean (d : Nat) (positive : 0 < d) (ambient : A) : StreamState A d :=
  MachinePortReindex.clean d positive (ambient, MachineRegularOriginalRow.zeroBuffer)

def relationStateEquiv (A : Type) (d : Nat) :
    MachineRegularOriginalRow.State (A × Fin d) ≃ StreamState A d where
  toFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  invFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  left_inv _ := rfl
  right_inv _ := rfl

def streamRelationCopy (d : Nat) (source destination : K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d) :=
  MachineStateEquiv.statement (relationStateEquiv A d)
    (MachineRegularOriginalRow.relationCopyAt source destination exit)

theorem streamRelationCopy_step (d : Nat) (positive : 0 < d)
    (source destination : K) (different : source ≠ destination)
    (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (code : program label = streamRelationCopy d source destination exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base source = encodeWords (relationWords relation) ++ suffix) (ambient : A) :
    TM2.step program ⟨some label, streamClean d positive ambient, base⟩ =
      some ⟨exit, streamClean d positive ambient,
        Function.update (Function.update base source suffix) destination
          (encodeWords (relationWords relation) ++ base destination)⟩ := by
  have hraw := MachineRegularOriginalRow.relationCopy_step source destination different label exit
    (fun _ => MachineRegularOriginalRow.relationCopyAt source destination exit) rfl
    relation suffix base input (ambient, MachineFixedDivMod.residue d positive 0)
    MachineRegularOriginalRow.zeroBuffer none
  have haux := Option.some.inj hraw
  change some (TM2.stepAux (program label) (streamClean d positive ambient) base) = _
  rw [code, streamRelationCopy, MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (relationStateEquiv A d)
    (TM2.stepAux (MachineRegularOriginalRow.relationCopyAt source destination exit)
      (((ambient, MachineFixedDivMod.residue d positive 0),
        MachineRegularOriginalRow.zeroBuffer), none) base)) = _
  rw [haux]
  rfl

def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 10 => k.val) h

inductive StreamLabel (d : Nat)
  | tailStart | tailRead | reverseStart | reverseRead | copyRelation
  | row (stage : Label d)
  | clearTail | clearOld | clearRelation | clearNew
  deriving DecidableEq, Fintype

def streamInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : StreamLabel d → Λ) (exit : Option Λ) :
    StreamLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | .tailStart => Hastad.SourceMachine.fieldStart (tape 0) (labels .tailRead)
  | .tailRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 0) (labels .tailRead)
      (some (labels .reverseStart))
  | .reverseStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .reverseRead)
  | .reverseRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1) (labels .reverseRead)
      (some (labels .copyRelation))
  | .copyRelation => streamRelationCopy d (tape 9) (tape 2)
      (some (labels (.row (.inl .copySeed))))
  | .row stage => reindexInstruction d positive c b (tape ∘ bodyIndex)
      (fun stage => labels (.row stage)) (some (labels .clearTail)) stage
  | .clearTail => MachineDrain.drain (tape 0) (labels .clearTail) (some (labels .clearOld))
  | .clearOld => MachineDrain.drain (tape 1) (labels .clearOld) (some (labels .clearRelation))
  | .clearRelation => MachineDrain.drain (tape 2) (labels .clearRelation) (some (labels .clearNew))
  | .clearNew => MachineDrain.drain (tape 6) (labels .clearNew) exit

def inputRowBits (v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord j ++ encodeWords (relationWords relation)

def streamRowSteps (d c b v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  (v + 2) + (j + 2) + 1 + reindexSteps d c b v j relation output +
    (v + 2) + (j + 2) + ((encodeWords (relationWords relation)).length + 1) +
    (MachinePortReindex.value d c b j + 2)

def streamResultTapes (d c b v j : Nat) (relation : RelationTable)
    (tape : Fin 10 → K) (base : K → List Bool) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) suffix) (tape 7)
    (base (tape 7) ++ reindexRowBits d c b v j relation)

theorem joinTrace_inline_MachineLazyRows {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem streamRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : StreamLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = streamInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable) (suffix : List Bool)
    (input : base (tape 9) = inputRowBits v j relation ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A) :
    (advance (TM2.step program))^[streamRowSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamResultTapes d c b v j relation tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have hb6 : bodyIndex 6 = 6 := rfl
  have hb7 : bodyIndex 7 = 7 := rfl
  have h₀ := empty 0 (by decide) (by decide)
  have h₁ := empty 1 (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide)
  let relationBits := encodeWords (relationWords relation)
  let tailLoaded := Function.update (Function.update base (tape 9)
    (encodeWord j ++ (relationBits ++ suffix))) (tape 0) (encodeWord v)
  let reverseLoaded := Function.update (Function.update tailLoaded (tape 9)
    (relationBits ++ suffix)) (tape 1) (encodeWord j)
  let loaded := Function.update (Function.update reverseLoaded (tape 9) suffix) (tape 2) relationBits
  let rowed := reindexResultTapes d c b v j relation (tape ∘ bodyIndex) loaded
  let tailCleared := Function.update rowed (tape 0) []
  let oldCleared := Function.update tailCleared (tape 1) []
  let relationCleared := Function.update oldCleared (tape 2) []
  have tailRun : (advance (TM2.step program))^[v + 2]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 0) (hd 9 0 (by decide))
      (labels .tailStart) (labels .tailRead) (some (labels .reverseStart)) program
      (atLabels .tailStart) (atLabels .tailRead) base v
      (encodeWord j ++ (relationBits ++ suffix))
      (by simpa only [inputRowBits, List.append_assoc] using input)
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      h₀, List.append_nil] at h
    convert h using 1 <;> rfl
  have reverseRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩) =
      some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩ := by
    have hstart : tailLoaded (tape 1) = [] := by
      simp [tailLoaded, hd 1 0 (by decide), hd 1 9 (by decide), h₁]
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .reverseStart) (labels .reverseRead) (some (labels .copyRelation)) program
      (atLabels .reverseStart) (atLabels .reverseRead) tailLoaded j (relationBits ++ suffix)
      (by simp [tailLoaded, hd 9 0 (by decide)])
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      hstart, List.append_nil] at h
    convert h using 1 <;> rfl
  have copyRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩ := by
    have hempty : reverseLoaded (tape 2) = [] := by
      simp [reverseLoaded, tailLoaded, hd 2 1 (by decide), hd 2 9 (by decide),
        hd 2 0 (by decide), h₂]
    have h := streamRelationCopy_step d positive (tape 9) (tape 2) (hd 9 2 (by decide))
      (labels .copyRelation) (some (labels (.row (.inl .copySeed)))) program
      (atLabels .copyRelation) relation suffix reverseLoaded
      (by simp [reverseLoaded, relationBits, hd 9 1 (by decide)]) ambient
    simpa only [Function.iterate_one, advance_some, hempty, List.append_nil, loaded] using h
  have hs (i : Fin 10) (hi : i ≠ 0) (hi' : i ≠ 1) (hi'' : i ≠ 2) (hi''' : i ≠ 9) :
      loaded (tape i) = base (tape i) := by
    simp [loaded, reverseLoaded, tailLoaded, hd i 0 hi, hd i 1 hi',
      hd i 2 hi'', hd i 9 hi''']
  have loadedTail : loaded (tape 0) = encodeWord v := by
    simp [loaded, reverseLoaded, tailLoaded, hd 0 2 (by decide), hd 0 9 (by decide),
      hd 0 1 (by decide)]
  have loadedReverse : loaded (tape 1) = encodeWord j := by
    simp [loaded, reverseLoaded, hd 1 2 (by decide), hd 1 9 (by decide)]
  have loadedRelation : loaded (tape 2) = relationBits := by simp [loaded]
  have bodyRun := reindexRowTrace d positive c b (tape ∘ bodyIndex)
    (distinct.comp bodyIndex_injective) (fun stage => labels (.row stage))
    (some (labels .clearTail)) program (fun stage => atLabels (.row stage)) loaded v j relation
    loadedTail loadedReverse loadedRelation
    ((hs 3 (by decide) (by decide) (by decide) (by decide)).trans h₃)
    ((hs 4 (by decide) (by decide) (by decide) (by decide)).trans h₄)
    ((hs 5 (by decide) (by decide) (by decide) (by decide)).trans h₅)
    ((hs 6 (by decide) (by decide) (by decide) (by decide)).trans h₆)
    ((hs 8 (by decide) (by decide) (by decide) (by decide)).trans h₈)
    (ambient, MachineRegularOriginalRow.zeroBuffer)
  have hout : loaded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩) =
    some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩ at bodyRun
  have rowedTail : rowed (tape 0) = encodeWord v := by
    simp only [rowed, reindexResultTapes, reindexMappedTapes, Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 0 7 (by decide)),
      Function.update_of_ne (hd 0 6 (by decide))] using loadedTail
  have rowedOld : tailCleared (tape 1) = encodeWord j := by
    simp only [tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 1 0 (by decide)),
      Function.update_of_ne (hd 1 7 (by decide)), Function.update_of_ne (hd 1 6 (by decide))]
      using loadedReverse
  have rowedRelation : oldCleared (tape 2) = relationBits := by
    simp only [oldCleared, tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 2 1 (by decide)),
      Function.update_of_ne (hd 2 0 (by decide)), Function.update_of_ne (hd 2 7 (by decide)),
      Function.update_of_ne (hd 2 6 (by decide))] using loadedRelation
  have rowedNew : relationCleared (tape 6) = encodeWord (MachinePortReindex.value d c b j) := by
    simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
      reindexMappedTapes, Function.comp_apply, bodyIndex, hd 6 2 (by decide),
      hd 6 1 (by decide), hd 6 0 (by decide), hd 6 7 (by decide)]
  have clearTail := (MachineDrain.drainInTime (tape 0) (labels .clearTail)
    (some (labels .clearOld)) program (atLabels .clearTail) rowed
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 0)).length + 1]
    (some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩) =
    some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩ at clearTail
  rw [rowedTail, encodeWord_length] at clearTail
  have clearOld := (MachineDrain.drainInTime (tape 1) (labels .clearOld)
    (some (labels .clearRelation)) program (atLabels .clearOld) tailCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(tailCleared (tape 1)).length + 1]
    (some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩) =
    some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩ at clearOld
  rw [rowedOld, encodeWord_length] at clearOld
  have clearRelation := (MachineDrain.drainInTime (tape 2) (labels .clearRelation)
    (some (labels .clearNew)) program (atLabels .clearRelation) oldCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 2)).length + 1]
    (some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩) =
    some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩ at clearRelation
  rw [rowedRelation] at clearRelation
  have clearNew := (MachineDrain.drainInTime (tape 6) (labels .clearNew)
    exit program (atLabels .clearNew) relationCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(relationCleared (tape 6)).length + 1]
    (some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩) =
    some ⟨exit, streamClean d positive ambient,
      Function.update relationCleared (tape 6) []⟩ at clearNew
  rw [rowedNew, encodeWord_length] at clearNew
  have finalFrame : Function.update relationCleared (tape 6) [] =
      streamResultTapes d c b v j relation tape base suffix := by
    funext k
    by_cases h6 : k = tape 6
    · subst k
      simp [streamResultTapes, hd 6 7 (by decide), hd 6 9 (by decide), h₆]
    · by_cases h2 : k = tape 2
      · subst k
        simp [relationCleared, streamResultTapes, hd 2 6 (by decide),
          hd 2 7 (by decide), hd 2 9 (by decide), h₂]
      · by_cases h1 : k = tape 1
        · subst k
          simp [relationCleared, oldCleared, streamResultTapes,
            hd 1 6 (by decide), hd 1 2 (by decide), hd 1 7 (by decide),
            hd 1 9 (by decide), h₁]
        · by_cases h0 : k = tape 0
          · subst k
            simp [relationCleared, oldCleared, tailCleared, streamResultTapes,
              hd 0 6 (by decide), hd 0 2 (by decide), hd 0 1 (by decide),
              hd 0 7 (by decide), hd 0 9 (by decide), h₀]
          · by_cases h7 : k = tape 7
            · subst k
              simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                reindexMappedTapes, Function.comp_apply, bodyIndex, streamResultTapes,
                loaded, reverseLoaded, tailLoaded, hd 7 6 (by decide), hd 7 2 (by decide),
                hd 7 1 (by decide), hd 7 0 (by decide), hd 7 9 (by decide)]
            · by_cases h9 : k = tape 9
              · subst k
                simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, hd 9 6 (by decide), hd 9 2 (by decide),
                  hd 9 1 (by decide), hd 9 0 (by decide), hd 9 7 (by decide)]
              · simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, h6, h2, h1, h0, h7, h9]
  rw [finalFrame] at clearNew
  exact joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows
    (joinTrace_inline_MachineLazyRows tailRun reverseRun) copyRun) bodyRun) clearTail) clearOld) clearRelation) clearNew

end DFVSGames.Foundations.Complexity.MachineLazyRows
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
