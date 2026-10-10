import OAI.Computability.BinPacking.CookLevin.ValidityMachine

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

namespace Full

def rowMap : Fin 7 ↪ Fin 10 := ⟨![2, 3, 4, 5, 6, 7, 8], by decide⟩

structure Ready (slots : Fin 10 ↪ K) (base : K → List Bool) (q : Nat) : Prop where
  source : base (slots 0) = encodeWord q
  empty : ∀ k : Fin 10, k ≠ 0 → k ≠ 7 → k ≠ 8 → base (slots k) = []

theorem Ready.emitted {slots : Fin 10 ↪ K} {base : K → List Bool} {q : Nat}
    (h : Ready slots base q) (tokens : List Token) :
    Ready slots (emitted (slots 7) (slots 8) base tokens) q := by
  constructor
  · simpa [ClashMachine.emitted, slots.injective.eq_iff] using h.source
  · intro k hk ho hc
    simpa [ClashMachine.emitted, slots.injective.eq_iff, ho, hc] using h.empty k hk ho hc

theorem ext_slots {n : Nat} (slots : Fin n ↪ K) (f g : K → List Bool)
    (atSlot : ∀ i, f (slots i) = g (slots i))
    (outside : ∀ k, (∀ i, k ≠ slots i) → f k = g k) : f = g := by
  classical
  funext k
  by_cases h : ∃ i, slots i = k
  · rcases h with ⟨i, rfl⟩
    exact atSlot i
  · exact outside k (fun i hi => h ⟨i, hi.symm⟩)

def frame (slots : Fin 10 ↪ K) (base : K → List Bool) (remaining current : Nat) : K → List Bool :=
  Function.update (Function.update base (slots 1) (encodeWord remaining)) (slots 3) (encodeWord current)

def closurePorts (slots : Fin 10 ↪ K) : OrClosure.Ports K where
  remaining := slots 9
  reversed := slots 7
  count := slots 8
  remaining_ne_reversed := slots.injective.ne (by decide)
  remaining_ne_count := slots.injective.ne (by decide)
  reversed_ne_count := slots.injective.ne (by decide)

inductive CopyContext where
  | outer | inner | rowClose | allClose
  deriving DecidableEq

instance : Fintype CopyContext where
  elems := { .outer, .inner, .rowClose, .allClose }
  complete c := by cases c <;> simp

inductive CopyLabel where
  | seed | scan | restore
  deriving DecidableEq

instance : Fintype CopyLabel where
  elems := { .seed, .scan, .restore }
  complete l := by cases l <;> simp

inductive Label where
  | start
  | copy (context : CopyContext) (l : CopyLabel)
  | outerGuard | rowSeed
  | row (l : Row.Label)
  | discardInner | afterInner | rowCloseSeed | rowCloseLoop | rowFinish
  | allCloseSeed | allCloseLoop | discardOuter | finish
  deriving DecidableEq, Fintype

def copyTarget (slots : Fin 10 ↪ K) : CopyContext → K
  | .outer => slots 1
  | .inner => slots 2
  | .rowClose | .allClose => slots 9

def copyExit (labels : Label → Λ) : CopyContext → Λ
  | .outer => labels .outerGuard
  | .inner => labels (.row .guard)
  | .rowClose => labels .rowCloseSeed
  | .allClose => labels .allCloseSeed

def statement (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => .push (slots 3) (fun _ => false) (.goto fun _ => labels (.copy .outer .seed))
  | .copy c .seed => MachineUnaryAffineAt.seed (copyTarget slots c) 1 (labels (.copy c .scan))
  | .copy c .scan => MachineUnaryAffineAt.scan (slots 0) (slots 5) (copyTarget slots c) 1
      (labels (.copy c .scan)) (labels (.copy c .restore))
  | .copy c .restore => Reduction.MachineTransfer.loopAt (slots 5) (slots 0) id false
      (labels (.copy c .restore)) (some (copyExit labels c))
  | .outerGuard => MachineUnaryCounter.guard (slots 1) (labels .rowSeed) (labels (.copy .allClose .seed))
  | .rowSeed => .push (slots 4) (fun _ => false) (.goto fun _ => labels (.copy .inner .seed))
  | .row l => Row.statement (rowMap.trans slots) (fun l => labels (.row l)) (labels .discardInner) l
  | .discardInner => MachineLookup.discard (slots 4) (labels .discardInner) (labels .afterInner)
  | .afterInner => .pop (slots 2) (fun s _ => s) (.goto fun _ => labels (.copy .rowClose .seed))
  | .rowCloseSeed => OrClosure.seed (closurePorts slots) (labels .rowCloseLoop)
  | .rowCloseLoop => OrClosure.loop (closurePorts slots) (labels .rowCloseLoop) (some (labels .rowFinish))
  | .rowFinish => .pop (slots 9) (fun s _ => s)
      (.push (slots 3) (fun _ => true) (.goto fun _ => labels .outerGuard))
  | .allCloseSeed => OrClosure.seed (closurePorts slots) (labels .allCloseLoop)
  | .allCloseLoop => OrClosure.loop (closurePorts slots) (labels .allCloseLoop) (some (labels .discardOuter))
  | .discardOuter => MachineLookup.discard (slots 3) (labels .discardOuter) (labels .finish)
  | .finish => .pop (slots 1) (fun s _ => s) (.pop (slots 9) (fun s _ => s)
      (Reduction.MachineTransfer.exitAt (slots 7) exit))

def copySteps (q : Nat) : Nat := 2 * (q + 1) + 1

theorem copyTrace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (context : CopyContext) (base : K → List Bool) (q : Nat)
    (sourceWord : base (slots 0) = encodeWord q) (scratchEmpty : base (slots 5) = [])
    (targetEmpty : base (copyTarget slots context) = []) (ambient : σ) :
    (advance (TM2.step program))^[copySteps q]
      (some ⟨some (labels (.copy context .seed)), clean ambient, base⟩) =
      some ⟨some (copyExit labels context), clean ambient,
        Function.update base (copyTarget slots context) (encodeWord (q + 1))⟩ := by
  have hd : slots 0 ≠ copyTarget slots context := by
    cases context <;> simp [copyTarget, slots.injective.eq_iff]
  have hs : slots 5 ≠ copyTarget slots context := by
    cases context <;> simp [copyTarget, slots.injective.eq_iff]
  have h := MachineUnaryAffineAt.seededAffineTrace (slots 0) (slots 5) (copyTarget slots context)
    (slots.injective.ne (by decide)) hd hs 1 1 (labels (.copy context .seed))
    (labels (.copy context .scan)) (labels (.copy context .restore))
    (some (copyExit labels context)) program (atLabels _) (atLabels _) (atLabels _)
    base q [] (by simpa using sourceWord) scratchEmpty (ambient, false) none
  simpa only [copySteps, clean, one_mul, targetEmpty, List.append_nil] using h

theorem closureTrace (slots : Fin 10 ↪ K) (entry again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atSeed : program entry = OrClosure.seed (closurePorts slots) again)
    (atLoop : program again = OrClosure.loop (closurePorts slots) again exit)
    (base : K → List Bool) (n : Nat) (word : base (slots 9) = encodeWord n) (ambient : σ) :
    (advance (TM2.step program))^[n + 2]
      (some ⟨some entry, clean ambient, base⟩) =
      some ⟨exit, clean ambient, Function.update
        (emitted (slots 7) (slots 8) base (closeOr n)) (slots 9) (encodeWord 0)⟩ := by
  have h := OrClosure.closureTrace (closurePorts slots) entry again exit program atSeed atLoop
    base n [] (base (slots 7)) (base (slots 8)) (ambient, false) none
  have hi : OrClosure.frame (closurePorts slots) base (encodeWord n ++ [])
      (base (slots 7)) (base (slots 8)) = base := by
    rw [List.append_nil, ← word]
    exact OrClosure.frame_self _ _
  have ho : OrClosure.frame (closurePorts slots) base (encodeWord 0 ++ [])
      ((tokenBits (closeOr n)).reverse ++ base (slots 7))
      (List.replicate (n + 1) true ++ base (slots 8)) =
      Function.update (emitted (slots 7) (slots 8) base (closeOr n)) (slots 9) (encodeWord 0) := by
    apply ext_slots slots
    · intro i
      fin_cases i <;> simp [OrClosure.frame, closurePorts, emitted, closeOr, slots.injective.eq_iff]
    · intro k hk
      simp [OrClosure.frame, closurePorts, emitted, hk]
  rw [hi, ho] at h
  exact h

theorem emitted_frame (slots : Fin 10 ↪ K) (base : K → List Bool) (r i : Nat) (tokens : List Token) :
    emitted (slots 7) (slots 8) (frame slots base r i) tokens =
      frame slots (emitted (slots 7) (slots 8) base tokens) r i := by
  apply ext_slots slots
  · intro k
    fin_cases k <;> simp [frame, emitted, slots.injective.eq_iff]
  · intro k hk
    simp [frame, emitted, hk]

def bodySteps (q i : Nat) : Nat :=
  1 + copySteps q + Row.steps (q + 1) i 0 + (q + 2) + 1 + copySteps q + (q + 3) + 1

theorem bodySteps_eq (q i : Nat) : bodySteps q i = Row.steps (q + 1) i 0 + 6 * q + 14 := by
  unfold bodySteps copySteps
  omega

theorem bodyTrace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q r i : Nat) (ready : Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[bodySteps q i]
      (some ⟨some (labels .rowSeed), clean ambient, frame slots base r i⟩) =
      some ⟨some (labels .outerGuard), clean ambient,
        frame slots (emitted (slots 7) (slots 8) base (clashRowTokens q i)) r (i + 1)⟩ := by
  let initial := frame slots base r i
  let seeded := Function.update initial (slots 4) (encodeWord 0)
  have hseed : (advance (TM2.step program))^[1]
      (some ⟨some (labels .rowSeed), clean ambient, initial⟩) =
      some ⟨some (labels (.copy .inner .seed)), clean ambient, seeded⟩ := by
    change some (TM2.stepAux (program (labels .rowSeed)) _ _) = _
    rw [atLabels, statement]
    simp [TM2.stepAux, seeded, initial, frame, slots.injective.eq_iff,
      ready.empty 4 (by decide) (by decide) (by decide), encodeWord]
  have hq : seeded (slots 0) = encodeWord q := by
    simpa [seeded, initial, frame, slots.injective.eq_iff] using ready.source
  have hs : seeded (slots 5) = [] := by
    simpa [seeded, initial, frame, slots.injective.eq_iff] using
      ready.empty 5 (by decide) (by decide) (by decide)
  have ht : seeded (copyTarget slots .inner) = [] := by
    simpa [copyTarget, seeded, initial, frame, slots.injective.eq_iff] using
      ready.empty 2 (by decide) (by decide) (by decide)
  have hcopy := copyTrace slots labels exit program atLabels .inner seeded q hq hs ht ambient
  have hstart : Function.update seeded (copyTarget slots .inner) (encodeWord (q + 1)) =
      Row.frame (rowMap.trans slots) initial (q + 1) 0 := by
    change Function.update (Function.update initial (slots 4) (encodeWord 0))
      (slots 2) (encodeWord (q + 1)) =
      Function.update (Function.update initial (slots 2) (encodeWord (q + 1)))
        (slots 4) (encodeWord 0)
    exact Function.update_comm (slots.injective.ne (by decide : (4 : Fin 10) ≠ 2)) _ _ _
  rw [hstart] at hcopy
  have hi : initial (slots 3) = encodeWord i := by simp [initial, frame]
  have hsl : initial (slots 5) = [] := by
    simpa [initial, frame, slots.injective.eq_iff] using
      ready.empty 5 (by decide) (by decide) (by decide)
  have hsr : initial (slots 6) = [] := by
    simpa [initial, frame, slots.injective.eq_iff] using
      ready.empty 6 (by decide) (by decide) (by decide)
  have hrow := Row.trace (rowMap.trans slots) (fun l => labels (.row l))
    (labels .discardInner) program (fun _ => atLabels _) initial (q + 1) i 0 hi hsl hsr ambient
  simp only [Nat.zero_add] at hrow
  let innerTokens := Row.tokens (q + 1) i 0
  let innerBase := emitted (slots 7) (slots 8) base innerTokens
  have innerReady : Ready slots innerBase q := ready.emitted innerTokens
  let afterRow := Row.frame (rowMap.trans slots) (frame slots innerBase r i) 0 (q + 1)
  change (advance (TM2.step program))^[Row.steps (q + 1) i 0]
    (some ⟨some (labels (.row .guard)), clean ambient, Row.frame (rowMap.trans slots) initial (q + 1) 0⟩) =
    some ⟨some (labels .discardInner), clean ambient,
      Row.frame (rowMap.trans slots) (emitted (slots 7) (slots 8) initial innerTokens) 0 (q + 1)⟩ at hrow
  have hemit : emitted (slots 7) (slots 8) initial innerTokens = frame slots innerBase r i :=
    emitted_frame slots base r i innerTokens
  rw [hemit] at hrow
  have hj : afterRow (slots 4) = encodeWord (q + 1) := by simp [afterRow, Row.frame, rowMap]
  have hdiscard := MachineLookup.discardTrace (slots 4) (labels .discardInner) (labels .afterInner)
    program (atLabels .discardInner) afterRow (q + 1) [] (by simpa using hj) (ambient, false) none
  have hclean : (advance (TM2.step program))^[1]
      (some ⟨some (labels .afterInner), clean ambient, Function.update afterRow (slots 4) []⟩) =
      some ⟨some (labels (.copy .rowClose .seed)), clean ambient, frame slots innerBase r i⟩ := by
    change some (TM2.stepAux (program (labels .afterInner)) _ _) = _
    rw [atLabels, statement]
    simp only [TM2.stepAux]
    congr 2
    apply ext_slots slots
    · intro k
      fin_cases k <;> simp [afterRow, Row.frame, rowMap, frame, slots.injective.eq_iff,
        encodeWord, innerReady.empty 2 (by decide) (by decide) (by decide),
        innerReady.empty 4 (by decide) (by decide) (by decide)]
    · intro k hk
      simp [afterRow, Row.frame, rowMap, frame, hk]
  have hcq : frame slots innerBase r i (slots 0) = encodeWord q := by
    simpa [frame, slots.injective.eq_iff] using innerReady.source
  have hcs : frame slots innerBase r i (slots 5) = [] := by
    simpa [frame, slots.injective.eq_iff] using innerReady.empty 5 (by decide) (by decide) (by decide)
  have hct : frame slots innerBase r i (copyTarget slots .rowClose) = [] := by
    simpa [frame, copyTarget, slots.injective.eq_iff] using
      innerReady.empty 9 (by decide) (by decide) (by decide)
  have hcCopy := copyTrace slots labels exit program atLabels .rowClose
    (frame slots innerBase r i) q hcq hcs hct ambient
  let closeStart := Function.update (frame slots innerBase r i) (slots 9) (encodeWord (q + 1))
  have hclose := closureTrace slots (labels .rowCloseSeed) (labels .rowCloseLoop)
    (some (labels .rowFinish)) program (atLabels .rowCloseSeed) (atLabels .rowCloseLoop)
    closeStart (q + 1) (by simp [closeStart]) ambient
  let closeEnd := Function.update (emitted (slots 7) (slots 8) closeStart (closeOr (q + 1)))
    (slots 9) (encodeWord 0)
  let closeBase := emitted (slots 7) (slots 8) innerBase (closeOr (q + 1))
  have hfinish : (advance (TM2.step program))^[1]
      (some ⟨some (labels .rowFinish), clean ambient, closeEnd⟩) =
      some ⟨some (labels .outerGuard), clean ambient, frame slots closeBase r (i + 1)⟩ := by
    change some (TM2.stepAux (program (labels .rowFinish)) _ _) = _
    rw [atLabels, statement]
    simp only [TM2.stepAux]
    congr 2
    apply ext_slots slots
    · intro k
      fin_cases k <;> simp [closeEnd, closeStart, closeBase, emitted, frame, slots.injective.eq_iff,
        encodeWord, List.replicate_succ, innerReady.empty 9 (by decide) (by decide) (by decide)]
    · intro k hk
      simp [closeEnd, closeStart, closeBase, emitted, frame, hk]
  have h := chain (chain (chain (chain (chain (chain (chain hseed hcopy) hrow) hdiscard) hclean)
    hcCopy) hclose) hfinish
  have hout : closeBase = emitted (slots 7) (slots 8) base (clashRowTokens q i) := by
    rw [show closeBase = emitted (slots 7) (slots 8)
      (emitted (slots 7) (slots 8) base innerTokens) (closeOr (q + 1)) from rfl,
      emitted_append (slots 7) (slots 8) (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8))]
    simp [clashRowTokens, innerTokens, Row.tokens]
  rw [hout] at h
  exact h

theorem counter_frame (slots : Fin 10 ↪ K) (base : K → List Bool) (r r' i : Nat) :
    MachineUnaryCounter.counterTapes (slots 1) (frame slots base r i) r' [] = frame slots base r' i := by
  apply ext_slots slots
  · intro k
    fin_cases k <;> simp [MachineUnaryCounter.counterTapes, frame, slots.injective.eq_iff]
  · intro k hk
    simp [MachineUnaryCounter.counterTapes, frame, hk]

def loopTokens (count q start : Nat) : List Token :=
  forTokens count (fun j => clashRowTokens q (start + j))

theorem loopTokens_succ (count q start : Nat) :
    loopTokens (count + 1) q start = clashRowTokens q start ++ loopTokens count q (start + 1) := by
  rw [loopTokens, forTokens_succ_first]
  simp only [Nat.add_zero]
  apply congrArg (List.append (clashRowTokens q start))
  apply forTokens_congr
  intro j _
  rw [show start + (j + 1) = start + 1 + j by omega]

def loopSteps : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | count + 1, q, start => 1 + bodySteps q start + loopSteps count q (start + 1)

theorem loopTrace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q count start : Nat) (ready : Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[loopSteps count q start]
      (some ⟨some (labels .outerGuard), clean ambient, frame slots base count start⟩) =
      some ⟨some (labels (.copy .allClose .seed)), clean ambient,
        frame slots (emitted (slots 7) (slots 8) base (loopTokens count q start)) 0 (start + count)⟩ := by
  induction count generalizing base start with
  | zero =>
    have h := MachineUnaryCounter.guardTrace_zero (slots 1) (labels .outerGuard)
      (labels .rowSeed) (labels (.copy .allClose .seed)) program (atLabels .outerGuard)
      (frame slots base 0 start) [] (ambient, false) none
    simpa only [counter_frame, loopSteps, loopTokens, forTokens, emitted_nil, Nat.add_zero, clean] using h
  | succ count ih =>
    have hg := MachineUnaryCounter.guardTrace_succ (slots 1) (labels .outerGuard)
      (labels .rowSeed) (labels (.copy .allClose .seed)) program (atLabels .outerGuard)
      (frame slots base count start) count [] (ambient, false) none
    simp only [counter_frame] at hg
    have hb := bodyTrace slots labels exit program atLabels base q count start ready ambient
    let nextBase := emitted (slots 7) (slots 8) base (clashRowTokens q start)
    have hr := ih nextBase (start + 1) (ready.emitted (clashRowTokens q start))
    have h := chain (chain hg hb) hr
    rw [show start + 1 + count = start + (count + 1) by omega] at h
    simp only [nextBase,
      emitted_append (slots 7) (slots 8) (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8)),
      ← loopTokens_succ] at h
    exact h

def bodyBudget (q : Nat) : Nat := (q + 1) * (12 * (2 * q + 3) + 2) + 1 + 6 * q + 14

theorem bodySteps_le (q i : Nat) (hi : i ≤ q) : bodySteps q i ≤ bodyBudget q := by
  have h := Row.steps_le (q + 1) i 0 (2 * q + 1) (by omega)
  rw [bodySteps_eq]
  unfold bodyBudget
  have he : 12 * (2 * q + 1 + 2) + 2 = 12 * (2 * q + 3) + 2 := by omega
  rw [he] at h
  omega

theorem loopSteps_le (count q start : Nat) (hbound : start + count ≤ q + 1) :
    loopSteps count q start ≤ count * (bodyBudget q + 1) + 1 := by
  induction count generalizing start with
  | zero => simp [loopSteps]
  | succ count ih =>
    have hr := ih (start + 1) (by omega)
    have hb := bodySteps_le q start (by omega)
    rw [loopSteps, Nat.succ_mul]
    omega

def steps (q : Nat) : Nat :=
  1 + copySteps q + loopSteps (q + 1) q 0 + copySteps q + (q + 3) + (q + 2) + 1

theorem trace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[steps q]
      (some ⟨some (labels .start), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (clashTokens q)⟩ := by
  let seeded := Function.update base (slots 3) (encodeWord 0)
  have hstart : (advance (TM2.step program))^[1]
      (some ⟨some (labels .start), clean ambient, base⟩) =
      some ⟨some (labels (.copy .outer .seed)), clean ambient, seeded⟩ := by
    change some (TM2.stepAux (program (labels .start)) _ _) = _
    rw [atLabels, statement]
    simp [TM2.stepAux, seeded, ready.empty 3 (by decide) (by decide) (by decide), encodeWord]
  have hs : seeded (slots 0) = encodeWord q := by
    simpa [seeded, slots.injective.eq_iff] using ready.source
  have hw : seeded (slots 5) = [] := by
    simpa [seeded, slots.injective.eq_iff] using ready.empty 5 (by decide) (by decide) (by decide)
  have hd : seeded (copyTarget slots .outer) = [] := by
    simpa [seeded, copyTarget, slots.injective.eq_iff] using
      ready.empty 1 (by decide) (by decide) (by decide)
  have hcopy := copyTrace slots labels exit program atLabels .outer seeded q hs hw hd ambient
  have hframe : Function.update seeded (copyTarget slots .outer) (encodeWord (q + 1)) =
      frame slots base (q + 1) 0 := by
    apply ext_slots slots
    · intro k
      fin_cases k <;> simp [seeded, copyTarget, frame, slots.injective.eq_iff]
    · intro k hk
      simp [seeded, copyTarget, frame, hk]
  rw [hframe] at hcopy
  have hloop := loopTrace slots labels exit program atLabels base q (q + 1) 0 ready ambient
  simp only [Nat.zero_add] at hloop
  let loopBase := emitted (slots 7) (slots 8) base (loopTokens (q + 1) q 0)
  have loopReady : Ready slots loopBase q := ready.emitted _
  let afterLoop := frame slots loopBase 0 (q + 1)
  have hcq : afterLoop (slots 0) = encodeWord q := by
    simpa [afterLoop, frame, slots.injective.eq_iff] using loopReady.source
  have hcw : afterLoop (slots 5) = [] := by
    simpa [afterLoop, frame, slots.injective.eq_iff] using loopReady.empty 5 (by decide) (by decide) (by decide)
  have hcd : afterLoop (copyTarget slots .allClose) = [] := by
    simpa [afterLoop, frame, copyTarget, slots.injective.eq_iff] using
      loopReady.empty 9 (by decide) (by decide) (by decide)
  have hcopyEnd := copyTrace slots labels exit program atLabels .allClose afterLoop q hcq hcw hcd ambient
  let closeStart := Function.update afterLoop (slots 9) (encodeWord (q + 1))
  have hclose := closureTrace slots (labels .allCloseSeed) (labels .allCloseLoop)
    (some (labels .discardOuter)) program (atLabels .allCloseSeed) (atLabels .allCloseLoop)
    closeStart (q + 1) (by simp [closeStart]) ambient
  let closeEnd := Function.update (emitted (slots 7) (slots 8) closeStart (closeOr (q + 1)))
    (slots 9) (encodeWord 0)
  have hi : closeEnd (slots 3) = encodeWord (q + 1) := by
    simp [closeEnd, closeStart, afterLoop, frame, emitted, slots.injective.eq_iff]
  have hdiscard := MachineLookup.discardTrace (slots 3) (labels .discardOuter) (labels .finish)
    program (atLabels .discardOuter) closeEnd (q + 1) [] (by simpa using hi) (ambient, false) none
  let finalBase := emitted (slots 7) (slots 8) loopBase (closeOr (q + 1))
  have hfinish : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean ambient, Function.update closeEnd (slots 3) []⟩) =
      some ⟨exit, clean ambient, finalBase⟩ := by
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels, statement]
    have ht : Function.update (Function.update (Function.update closeEnd (slots 3) [])
        (slots 1) []) (slots 9) [] = finalBase := by
      apply ext_slots slots
      · intro k
        fin_cases k <;> simp [closeEnd, closeStart, afterLoop, finalBase, frame, emitted,
          slots.injective.eq_iff, loopReady.empty 1 (by decide) (by decide) (by decide),
          loopReady.empty 3 (by decide) (by decide) (by decide),
          loopReady.empty 9 (by decide) (by decide) (by decide)]
      · intro k hk
        simp [closeEnd, closeStart, afterLoop, finalBase, frame, emitted, hk]
    have hr : (Function.update closeEnd (slots 3) []) (slots 1) = encodeWord 0 := by
      simp [closeEnd, closeStart, afterLoop, frame, emitted, slots.injective.eq_iff]
    have hc : (Function.update (Function.update closeEnd (slots 3) []) (slots 1) []) (slots 9) =
        encodeWord 0 := by simp [closeEnd, slots.injective.eq_iff]
    simp only [TM2.stepAux, hr, hc, encodeWord, List.replicate_zero,
      List.nil_append, List.tail_cons, ht]
    cases exit <;> rfl
  have h := chain (chain (chain (chain (chain (chain hstart hcopy) hloop) hcopyEnd) hclose) hdiscard) hfinish
  have hout : finalBase = emitted (slots 7) (slots 8) base (clashTokens q) := by
    rw [show finalBase = emitted (slots 7) (slots 8)
      (emitted (slots 7) (slots 8) base (loopTokens (q + 1) q 0)) (closeOr (q + 1)) from rfl,
      emitted_append (slots 7) (slots 8) (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8))]
    simp [clashTokens, loopTokens]
  rw [hout] at h
  exact h

noncomputable def bodyPolynomial : Polynomial Nat :=
  (Polynomial.X + Polynomial.C 1) *
    (Polynomial.C 12 * (Polynomial.C 2 * Polynomial.X + Polynomial.C 3) + Polynomial.C 2) +
    Polynomial.C 1 + Polynomial.C 6 * Polynomial.X + Polynomial.C 14

noncomputable def timePolynomial : Polynomial Nat :=
  (Polynomial.X + Polynomial.C 1) * (bodyPolynomial + Polynomial.C 1) +
    Polynomial.C 1 + Polynomial.C 6 * Polynomial.X + Polynomial.C 13

theorem timePolynomial_eval (q : Nat) :
    timePolynomial.eval q = (q + 1) * (bodyBudget q + 1) + 1 + 6 * q + 13 := by
  simp [timePolynomial, bodyPolynomial, bodyBudget]

theorem steps_le_time (q : Nat) : steps q ≤ timePolynomial.eval q := by
  have h := loopSteps_le (q + 1) q 0 (by omega)
  rw [timePolynomial_eval]
  unfold steps copySteps
  omega

def inTime (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : Ready slots base q) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .start), clean ambient, base⟩
      (some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (clashTokens q)⟩)
      (timePolynomial.eval q) where
  steps := steps q
  evals_in_steps := trace slots labels exit program atLabels base q ready ambient
  steps_le_m := steps_le_time q

abbrev machine : FinTM2 where
  K := Fin 10
  k₀ := 0
  k₁ := 7
  Γ _ := Bool
  Λ := Label
  main := .start
  σ := State Unit
  initialState := clean ()
  m := statement (Function.Embedding.refl _) id none

def machineInTime (base : Fin 10 → List Bool) (q : Nat)
    (ready : Ready (Function.Embedding.refl _) base q) :
    StateTransition.EvalsToInTime machine.step ⟨some .start, clean (), base⟩
      (some ⟨none, clean (), emitted 7 8 base (clashTokens q)⟩) (timePolynomial.eval q) :=
  inTime (Function.Embedding.refl _) id none machine.m (fun _ => rfl) base q ready ()

end Full

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted)

variable {K Λ σ : Type} [DecidableEq K]

def nonemptyMap : Fin 7 ↪ Fin 10 := ⟨![0, 1, 3, 5, 9, 7, 8], by decide⟩

inductive Label where
  | nonempty (l : Nonempty.Label)
  | clash (l : ClashMachine.Full.Label)
  | finish
  deriving DecidableEq, Fintype

def statement (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (ValidityMachine.Alphabet (K := K)) Λ (State σ)
  | .nonempty l => Nonempty.statement (nonemptyMap.trans slots)
      (fun l => labels (.nonempty l)) (some (labels (.clash .start))) l
  | .clash l => ClashMachine.Full.statement slots (fun l => labels (.clash l))
      (some (labels .finish)) l
  | .finish => ClashMachine.literal (slots 7) (slots 8) [.not, .and]
      (Reduction.MachineTransfer.exitAt (slots 7) exit)

def steps (q : Nat) : Nat := Nonempty.steps q + ClashMachine.Full.steps q + 1

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X + Polynomial.C 2) ^ 2 +
    ClashMachine.Full.timePolynomial + Polynomial.C 1

theorem timePolynomial_eval (q : Nat) :
    timePolynomial.eval q = 20 * (q + 2) ^ 2 + ClashMachine.Full.timePolynomial.eval q + 1 := by
  simp [timePolynomial]

theorem steps_le_time (q : Nat) : steps q ≤ timePolynomial.eval q := by
  rw [timePolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nonempty.steps_le q) (ClashMachine.Full.steps_le_time q)) 1

private theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

theorem trace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (ValidityMachine.Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : ClashMachine.Full.Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[steps q]
      (some ⟨some (labels (.nonempty .initialize)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (validityTokens q)⟩ := by
  have nr : Nonempty.Ready (nonemptyMap.trans slots) base q := {
    boundWord := ready.source
    remainingEmpty := ready.empty 1 (by decide) (by decide) (by decide)
    currentEmpty := ready.empty 3 (by decide) (by decide) (by decide)
    scratchEmpty := ready.empty 5 (by decide) (by decide) (by decide)
    closureEmpty := ready.empty 9 (by decide) (by decide) (by decide) }
  have hn := Nonempty.trace (nonemptyMap.trans slots) (fun l => labels (.nonempty l))
    (some (labels (.clash .start))) program (fun _ => atLabels _) base q nr ambient
  let afterNonempty := emitted (slots 7) (slots 8) base (nonemptyTokens q)
  change (advance (TM2.step program))^[Nonempty.steps q]
    (some ⟨some (labels (.nonempty .initialize)), clean ambient, base⟩) =
    some ⟨some (labels (.clash .start)), clean ambient, afterNonempty⟩ at hn
  have hc := ClashMachine.Full.trace slots (fun l => labels (.clash l))
    (some (labels .finish)) program (fun _ => atLabels _)
    afterNonempty q (ready.emitted (nonemptyTokens q)) ambient
  let afterClash := emitted (slots 7) (slots 8) afterNonempty (clashTokens q)
  have hf : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean ambient, afterClash⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) afterClash [.not, .and]⟩ := by
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8))]
    cases exit <;> rfl
  have h := chain (chain hn hc) hf
  simpa only [steps, afterClash, afterNonempty,
    ClashMachine.emitted_append (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8)), validityTokens] using h

def inTime (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (ValidityMachine.Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : ClashMachine.Full.Ready slots base q) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.nonempty .initialize)), clean ambient, base⟩
      (some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (validityTokens q)⟩)
      (timePolynomial.eval q) where
  steps := steps q
  evals_in_steps := by
    change (advance (TM2.step program))^[steps q] _ = _
    exact trace slots labels exit program atLabels base q ready ambient
  steps_le_m := steps_le_time q

variable [Fintype K] [Fintype σ]

def machine (slots : Fin 10 ↪ K) (ambient : σ) : FinTM2 where
  K := K
  k₀ := slots 0
  k₁ := slots 7
  Γ := ValidityMachine.Alphabet
  Λ := Label
  main := .nonempty .initialize
  σ := State σ
  initialState := clean ambient
  Γk₀Fin := inferInstance
  m := statement slots id none

theorem machineTrace (slots : Fin 10 ↪ K) (base : K → List Bool) (q : Nat)
    (ready : ClashMachine.Full.Ready slots base q) (ambient : σ) :
    (advance (machine slots ambient).step)^[steps q]
      (some ⟨some (.nonempty .initialize), clean ambient, base⟩) =
      some ⟨none, clean ambient, emitted (slots 7) (slots 8) base (validityTokens q)⟩ := by
  exact trace slots id none (machine slots ambient).m (fun _ => rfl) base q ready ambient

def machineInTime (slots : Fin 10 ↪ K) (base : K → List Bool) (q : Nat)
    (ready : ClashMachine.Full.Ready slots base q) (ambient : σ) :
    StateTransition.EvalsToInTime (machine slots ambient).step
      ⟨some (.nonempty .initialize), clean ambient, base⟩
      (some ⟨none, clean ambient, emitted (slots 7) (slots 8) base (validityTokens q)⟩)
      (timePolynomial.eval q) :=
  inTime slots id none (machine slots ambient).m (fun _ => rfl) base q ready ambient

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full

end OAI
