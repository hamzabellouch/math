import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineDrain
import OAI.Combinatorics.IndependentSets.Machines.MachineCloudRank

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineCloudSelect

open Turing MachineComposition
open MachineCloudCount (Row rowWords rowTime rowsHits tableRows)

abbrev BaseTape := MachineCloudCount.Tape
abbrev BaseAlphabet := MachineCloudCount.Alphabet
abbrev BaseState (σ : Type) := MachineCloudCount.State σ

inductive BaseLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | field | restore | done | clearWork | clearRank
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def skipLabel (i : Nat) : BaseLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .done

variable {σ : Type}

def baseProgram : BaseLabel → TM2.Stmt BaseAlphabet BaseLabel (BaseState σ)
  | .queryFirst => Reduction.MachineTransfer.loopAt .target .scratch id false
      .queryFirst (some .querySecond)
  | .querySecond => MachineCopy.forkLoop .scratch .target .spare false
      .querySecond (some .querySkip)
  | .querySkip => MachineLookup.discard .spare .querySkip .tableFirst
  | .tableFirst => Reduction.MachineTransfer.loopAt .original .scratch id false
      .tableFirst (some .tableSecond)
  | .tableSecond => MachineCopy.forkLoop .scratch .original .work false
      .tableSecond (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .field
  | .field => MachineCloudCount.fieldLoop .field .restore
  | .restore => Reduction.MachineTransfer.loopAt .scratch .target id false
      .restore (some .done)
  | .skip i => MachineLookup.discard .work (.skip i) (skipLabel (i.val + 1))
  | .clearWork => MachineDrain.drain .work .clearWork (some .clearRank)
  | .clearRank => MachineDrain.drain .spare .clearRank (some .done)
  | .done => .halt

theorem baseProgram_skip {i : Nat} (hi : i < 4097) :
    baseProgram (σ := σ) (skipLabel i) =
      MachineLookup.discard .work (skipLabel i) (skipLabel (i + 1)) := by
  simp only [skipLabel, dite_eq_left hi, baseProgram]

inductive Phase | checking | advancing | finishing
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.checking, .advancing, .finishing}
  complete phase := by cases phase <;> simp

inductive Control | initialize | dispatch
  deriving DecidableEq

instance : Fintype Control where
  elems := {.initialize, .dispatch}
  complete control := by cases control <;> simp

abbrev Tape := BaseTape ⊕ Unit
abbrev Alphabet : Tape → Type := MachineEmbedding.Alphabet BaseAlphabet (fun _ : Unit => Bool)
abbrev Label := BaseLabel ⊕ Control
abbrev State (σ : Type) := BaseState σ × Phase

def go (phase : Phase) (label : Label) : TM2.Stmt Alphabet Label (State σ) :=
  .load (fun s => ((s.1.1, none), phase)) (.goto fun _ => label)

def dispatcher : TM2.Stmt Alphabet Label (State σ) :=
  .branch (fun s => decide (s.2 = .checking))
    (.pop (.inl .count) (fun s bit => ((s.1.1, bit), s.2))
      (.branch (fun s => s.1.2.getD false)
        (.pop (.inl .spare) (fun s bit => ((s.1.1, bit), s.2))
          (.branch (fun s => s.1.2.getD false)
            (go .advancing (.inl (skipLabel 0)))
            (go .finishing (.inl .clearWork))))
        (go .advancing (.inl (skipLabel 0)))))
    (.branch (fun s => decide (s.2 = .advancing))
      (.push (.inr ()) (fun _ => true) (go .checking (.inl .field)))
      (.load (fun s => ((s.1.1, none), Phase.checking)) .halt))

def extra : Control → TM2.Stmt Alphabet Label (State σ)
  | .initialize => .push (.inr ()) (fun _ => false) (go .checking (.inl .queryFirst))
  | .dispatch => dispatcher

def program : Label → TM2.Stmt Alphabet Label (State σ) :=
  MachineEmbedding.program (some (.inr .dispatch)) baseProgram extra

def memory (original work target scratch hit rank position : List Bool) :
    ∀ k, List (Alphabet k) :=
  MachineEmbedding.tapes (MachineCloudCount.memory original work target scratch hit rank)
    (fun _ : Unit => position)

@[simp] theorem memory_inl (a b c d e f g : List Bool) (k : BaseTape) :
    memory a b c d e f g (.inl k) = MachineCloudCount.memory a b c d e f k := rfl
@[simp] theorem memory_position (a b c d e f g : List Bool) :
    memory a b c d e f g (.inr ()) = g := rfl

@[simp] theorem update_memory_hit (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) (.inl .count) x = memory a b c d x f g := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl
@[simp] theorem update_memory_rank (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) (.inl .spare) x = memory a b c d e x g := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl
@[simp] theorem update_memory_position (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) (.inr ()) x = memory a b c d e f x := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl

def cfg (label : Option Label) (phase : Phase)
    (original work target hit rank position : List Bool)
    (ambient : σ) (register : Option Bool) : TM2.Cfg Alphabet Label (State σ) :=
  ⟨label, (((ambient, false), register), phase), memory original work target [] hit rank position⟩

theorem liftTrace (phase : Phase) (position : List Bool) (n : Nat)
    (a b : TM2.Cfg BaseAlphabet BaseLabel (BaseState σ))
    (h : (advance (TM2.step baseProgram))^[n] (some a) = some b) :
    (advance (TM2.step (program (σ := σ))))^[n]
      (some (MachineEmbedding.configuration (some (.inr .dispatch)) phase
        (fun _ : Unit => position) a)) =
      some (MachineEmbedding.configuration (some (.inr .dispatch)) phase
        (fun _ : Unit => position) b) :=
  liftSuccessfulTrace (TM2.step baseProgram) (TM2.step program)
    (MachineEmbedding.configuration (some (.inr .dispatch)) phase (fun _ : Unit => position))
    (MachineEmbedding.step_simulation (some (.inr .dispatch)) phase
      (fun _ : Unit => position) baseProgram extra) n a b h

theorem compareTrace (original suffix targetSuffix rank position : List Bool)
    (x v : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[x + min x v + 3]
      (some (cfg (some (.inl .field)) .checking original (encodeWord x ++ suffix)
        (encodeWord v ++ targetSuffix) [] rank position ambient register)) =
      some (cfg (some (.inr .dispatch)) .checking original suffix
        (encodeWord v ++ targetSuffix) (List.replicate (if x = v then 1 else 0) true)
        rank position ambient none) := by
  have h := MachineCloudCount.preservingFieldTrace BaseLabel.field BaseLabel.restore BaseLabel.done
    baseProgram rfl rfl original suffix targetSuffix [] rank x v ambient register
  simp only [List.append_nil] at h
  have hhalt : (advance (TM2.step baseProgram))^[x + min x v + 3]
      (some ⟨some .field, ((ambient, false), register),
        MachineCloudCount.memory original (encodeWord x ++ suffix)
          (encodeWord v ++ targetSuffix) [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if x = v then 1 else 0) true) rank⟩ := by
    rw [show x + min x v + 3 = (x + min x v + 2) + 1 by omega,
      Function.iterate_succ_apply', h, advance_some]
    rfl
  convert liftTrace Phase.checking position _ _ _ hhalt using 1 <;> rfl

theorem dispatch_miss (original work target rank position : List Bool) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [] rank position ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing
        original work target [] rank position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step, cfg]

theorem dispatch_hit_succ (original work target rankSuffix position : List Bool)
    (rank : Nat) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [true] (encodeWord (rank + 1) ++ rankSuffix) position ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing original work target []
        (encodeWord rank ++ rankSuffix) position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord, List.replicate_succ]

theorem dispatch_hit_zero (original work target rankSuffix position : List Bool) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [true] (encodeWord 0 ++ rankSuffix) position ambient none) =
      some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rankSuffix position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord]

theorem advanceStep (original work target rank positionSuffix : List Bool)
    (position : Nat) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .advancing original work target []
      rank (encodeWord position ++ positionSuffix) ambient none) =
      some (cfg (some (.inl .field)) .checking original work target []
        rank (encodeWord (position + 1) ++ positionSuffix) ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord, List.replicate_succ]

theorem finishStep (original target position : List Bool) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .finishing
      original [] target [] [] position ambient none) =
      some (cfg none .checking original [] target [] [] position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step, cfg]

theorem initializeStep (original target output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program (cfg (some (.inr .initialize)) .checking
      original [] target [] [] output ambient register) =
      some (cfg (some (.inl .queryFirst)) .checking
        original [] target [] [] (encodeWord 0 ++ output) ambient none) := by
  simp [program, MachineEmbedding.program, extra, go, TM2.stepAux, TM2.step, cfg, encodeWord]

theorem skipTrace (fields : List Nat) (hwidth : fields.length = 4097)
    (original suffix target rank position : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords fields).length + 1]
      (some (cfg (some (.inl (skipLabel 0))) .advancing original
        (encodeWords fields ++ suffix) target [] rank position ambient none)) =
      some (cfg (some (.inr .dispatch)) .advancing
        original suffix target [] rank position ambient none) := by
  have h := MachineCloudCount.discardFieldsTrace skipLabel (baseProgram (σ := σ)) fields 0
    (by intro i hi; simpa only [Nat.zero_add] using baseProgram_skip (hwidth ▸ hi))
    original suffix target [] [] rank ambient false none
  have hnonempty : fields ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, skipLabel, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at h
  have raw : (advance (TM2.step baseProgram))^[(encodeWords fields).length + 1]
      (some ⟨some (skipLabel 0), ((ambient, false), none),
        MachineCloudCount.memory original (encodeWords fields ++ suffix) target [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original suffix target [] [] rank⟩ := by
    rw [Function.iterate_succ_apply']
    simp only [skipLabel, dite_eq_left (by decide : 0 < 4097)] at h ⊢
    rw [h, advance_some]
    rfl
  convert liftTrace Phase.advancing position _ _ _ raw using 1 <;> rfl

theorem rowSkipTrace (r : Row) (hwidth : r.2.length = 4097) (v rank position : Nat)
    (original suffix targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rowTime v r + 3]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix) []
        (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg (some (.inl .field)) .checking original suffix
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord (position + 1) ++ outputSuffix) ambient none) := by
  have hcompare := compareTrace original (encodeWords r.2 ++ suffix) targetSuffix
    (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
    (encodeWord position ++ outputSuffix) r.1 v ambient register
  have hdispatch : TM2.step program
      (cfg (some (.inr .dispatch)) .checking original (encodeWords r.2 ++ suffix)
        (encodeWord v ++ targetSuffix) (List.replicate (if r.1 = v then 1 else 0) true)
        (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing original (encodeWords r.2 ++ suffix)
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient none) := by
    by_cases hit : r.1 = v
    · simpa only [ite_eq_left hit, List.replicate_succ, List.replicate_zero] using
        dispatch_hit_succ original (encodeWords r.2 ++ suffix) (encodeWord v ++ targetSuffix)
          rankSuffix (encodeWord position ++ outputSuffix) rank ambient
    · simpa only [ite_eq_right hit, Nat.add_zero, List.replicate_zero] using
        dispatch_miss original (encodeWords r.2 ++ suffix) (encodeWord v ++ targetSuffix)
          (encodeWord rank ++ rankSuffix) (encodeWord position ++ outputSuffix) ambient
  have hskip := skipTrace r.2 hwidth original suffix (encodeWord v ++ targetSuffix)
    (encodeWord rank ++ rankSuffix) (encodeWord position ++ outputSuffix) ambient
  have ht : rowTime v r + 3 =
      1 + (((encodeWords r.2).length + 1) + (1 + (r.1 + min r.1 v + 3))) := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [ht, Function.iterate_add_apply _ 1,
    Function.iterate_add_apply _ ((encodeWords r.2).length + 1),
    Function.iterate_add_apply _ 1]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hcompare, Function.iterate_one, advance_some, hdispatch, hskip,
    advance_some]
  exact advanceStep original suffix (encodeWord v ++ targetSuffix)
    (encodeWord rank ++ rankSuffix) outputSuffix position ambient

def prefixTime (v : Nat) : List Row → Nat
  | [] => 0
  | r :: rs => prefixTime v rs + (rowTime v r + 3)

theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097)
    (v rank position : Nat) (original suffix targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v rs]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (rs.flatMap rowWords) ++ suffix) (encodeWord v ++ targetSuffix) []
        (encodeWord (rowsHits v rs + rank) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg (some (.inl .field)) .checking original suffix
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord (position + rs.length) ++ outputSuffix) ambient
        (if rs = [] then register else none)) := by
  induction rs generalizing position register with
  | nil => simp [prefixTime, rowsHits, encodeWords]
  | cons r rs ih =>
    have hrow := rowSkipTrace r (hwidth r (by simp)) v (rowsHits v rs + rank) position
      original (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix rankSuffix
      outputSuffix ambient register
    have hrest := ih (by intro x hx; exact hwidth x (by simp [hx])) (position + 1) none
    simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc]
    rw [Function.iterate_add_apply]
    have hi : (if r.1 = v then 1 else 0) + rowsHits v rs + rank =
        (rowsHits v rs + rank) + (if r.1 = v then 1 else 0) := by omega
    simp only [rowsHits, hi]
    rw [hrow]
    simpa only [ite_self, List.cons_ne_nil, ite_false, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

theorem cleanupTrace (original work target rank position : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[work.length + rank.length + 4]
      (some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rank position ambient none)) =
      some (cfg none .checking original [] target [] [] position ambient none) := by
  have hwork := MachineDrain.drainTrace MachineCloudCount.Tape.work BaseLabel.clearWork (some BaseLabel.clearRank)
    baseProgram rfl (MachineCloudCount.memory original work target [] [] rank) work
    (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hwork
  have hrank := MachineDrain.drainTrace MachineCloudCount.Tape.spare BaseLabel.clearRank (some BaseLabel.done)
    baseProgram rfl (MachineCloudCount.memory original [] target [] [] rank) rank
    (ambient, false) none
  simp only [MachineCloudRank.update_memory_spare] at hrank
  have raw : (advance (TM2.step baseProgram))^[work.length + rank.length + 3]
      (some ⟨some .clearWork, ((ambient, false), none),
        MachineCloudCount.memory original work target [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original [] target [] [] []⟩ := by
    rw [show work.length + rank.length + 3 =
        1 + ((rank.length + 1) + (work.length + 1)) by omega,
      Function.iterate_add_apply _ 1, Function.iterate_add_apply _ (rank.length + 1),
      hwork, hrank, Function.iterate_one, advance_some]
    rfl
  have lifted := liftTrace Phase.finishing position _ _ _ raw
  have h : (advance (TM2.step program))^[work.length + rank.length + 3]
      (some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rank position ambient none)) =
      some (cfg (some (.inr .dispatch)) .finishing
        original [] target [] [] position ambient none) := by
    convert lifted using 1 <;> rfl
  rw [show work.length + rank.length + 4 = (work.length + rank.length + 3) + 1 by omega,
    Function.iterate_succ_apply', h, advance_some]
  exact finishStep original target position ambient

theorem selectedTrace (v : Nat) (original work targetSuffix rankSuffix position : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original (encodeWord v ++ work)
        (encodeWord v ++ targetSuffix) [] (encodeWord 0 ++ rankSuffix) position ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] [] position ambient none) := by
  have hcompare := compareTrace original work targetSuffix (encodeWord 0 ++ rankSuffix)
    position v v ambient register
  simp only [ite_true, List.replicate_succ, List.replicate_zero] at hcompare
  rw [show 2 * v + work.length + rankSuffix.length + 8 =
      (work.length + rankSuffix.length + 4) + (1 + (v + min v v + 3)) by
        simp only [Nat.min_self]; omega,
    Function.iterate_add_apply _ (work.length + rankSuffix.length + 4),
    Function.iterate_add_apply _ 1, hcompare, Function.iterate_one, advance_some,
    dispatch_hit_zero]
  exact cleanupTrace original work (encodeWord v ++ targetSuffix) rankSuffix position ambient

abbrev queryWord := MachineCloudRank.queryWord

def prepareSteps (n m v rank : Nat) (rs : List Row) (querySuffix : List Bool) : Nat :=
  2 * ((queryWord v rank querySuffix).length + 1) + (v + 1) +
    2 * ((MachineCloudCount.inputWord n m rs).length + 1) + (n + 1) + (m + 1)

theorem prepareTrace (n m v rank : Nat) (rs : List Row)
    (querySuffix position : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prepareSteps n m v rank rs querySuffix]
      (some (cfg (some (.inl .queryFirst)) .checking (MachineCloudCount.inputWord n m rs)
        [] (queryWord v rank querySuffix) [] [] position ambient register)) =
      some (cfg (some (.inl .field)) .checking (MachineCloudCount.inputWord n m rs)
        (encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix) []
        (encodeWord rank ++ querySuffix) position ambient none) := by
  have hquery := MachineCopy.copyTrace MachineCloudCount.Tape.target MachineCloudCount.Tape.spare MachineCloudCount.Tape.scratch
    (by decide) (by decide) (by decide) false BaseLabel.queryFirst BaseLabel.querySecond
    (some BaseLabel.querySkip) baseProgram rfl rfl
    (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] []) rfl (ambient, false) register
  simp only [MachineCloudCount.memory_target, MachineCloudCount.memory_spare,
    List.append_nil, MachineCloudRank.update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace MachineCloudCount.Tape.spare BaseLabel.querySkip BaseLabel.tableFirst
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] (queryWord v rank querySuffix))
    v (encodeWord rank ++ querySuffix) rfl (ambient, false) none
  simp only [MachineCloudRank.update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace MachineCloudCount.Tape.original MachineCloudCount.Tape.work MachineCloudCount.Tape.scratch
    (by decide) (by decide) (by decide) false BaseLabel.tableFirst BaseLabel.tableSecond
    (some BaseLabel.headerFirst) baseProgram rfl rfl
    (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] (encodeWord rank ++ querySuffix))
    rfl (ambient, false) none
  simp only [MachineCloudCount.memory_original, MachineCloudCount.memory_work,
    List.append_nil, MachineCloudCount.update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace MachineCloudCount.Tape.work BaseLabel.headerFirst BaseLabel.headerSecond
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
      (MachineCloudCount.inputWord n m rs) (queryWord v rank querySuffix) [] []
      (encodeWord rank ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (MachineCloudCount.inputWord_eq n m rs) (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace MachineCloudCount.Tape.work BaseLabel.headerSecond BaseLabel.field
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
      (encodeWord m ++ encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix)
      [] [] (encodeWord rank ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hsecond
  have raw : (advance (TM2.step baseProgram))^[prepareSteps n m v rank rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
          (queryWord v rank querySuffix) [] [] []⟩) =
      some ⟨some .field, ((ambient, false), none),
        MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
          (encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix) [] []
          (encodeWord rank ++ querySuffix)⟩ := by
    rw [show prepareSteps n m v rank rs querySuffix =
        (m + 1) + ((n + 1) + (2 * ((MachineCloudCount.inputWord n m rs).length + 1) +
          ((v + 1) + 2 * ((queryWord v rank querySuffix).length + 1)))) by
          unfold prepareSteps; omega,
      Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
      Function.iterate_add_apply _ (2 * ((MachineCloudCount.inputWord n m rs).length + 1)),
      Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst]
    exact hsecond
  convert liftTrace Phase.checking position _ _ _ raw using 1 <;> rfl

theorem prefixSelectedTrace (preceding : List Row)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097) (v position : Nat)
    (original work targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
        (encodeWord v ++ targetSuffix) [] (encodeWord (rowsHits v preceding) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] []
        (encodeWord (position + preceding.length) ++ outputSuffix) ambient none) := by
  have hp := prefixTrace preceding hwidth v 0 position original (encodeWord v ++ work)
    targetSuffix rankSuffix outputSuffix ambient register
  simp only [Nat.add_zero] at hp
  have hs := selectedTrace v original work targetSuffix rankSuffix
    (encodeWord (position + preceding.length) ++ outputSuffix) ambient
    (if preceding = [] then register else none)
  rw [show prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8 =
      (2 * v + work.length + rankSuffix.length + 8) + prefixTime v preceding by omega,
    Function.iterate_add_apply, hp]
  exact hs

def totalSteps (n m v rank : Nat) (rs preceding : List Row)
    (work querySuffix : List Bool) : Nat :=
  prepareSteps n m v rank rs querySuffix + prefixTime v preceding +
    2 * v + work.length + querySuffix.length + 9

theorem fullTrace (n m v rank : Nat) (rs preceding : List Row) (work : List Bool)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097)
    (hword : encodeWords (rs.flatMap rowWords) =
      encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
    (hrank : rank = rowsHits v preceding) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalSteps n m v rank rs preceding work querySuffix]
      (some (cfg (some (.inr .initialize)) .checking (MachineCloudCount.inputWord n m rs)
        [] (queryWord v rank querySuffix) [] [] outputSuffix ambient register)) =
      some (cfg none .checking (MachineCloudCount.inputWord n m rs) []
        (queryWord v rank querySuffix) [] [] (encodeWord preceding.length ++ outputSuffix) ambient none) := by
  have hp := prepareTrace n m v rank rs querySuffix (encodeWord 0 ++ outputSuffix) ambient none
  have hs := prefixSelectedTrace preceding hwidth v 0 (MachineCloudCount.inputWord n m rs) work
    (encodeWord rank ++ querySuffix) querySuffix outputSuffix ambient none
  simp only [Nat.zero_add] at hs
  rw [← hrank, ← hword] at hs
  rw [show totalSteps n m v rank rs preceding work querySuffix =
      (prefixTime v preceding + 2 * v + work.length + querySuffix.length + 8) +
        (prepareSteps n m v rank rs querySuffix + 1) by unfold totalSteps; omega,
    Function.iterate_add_apply _ (prefixTime v preceding + 2 * v + work.length + querySuffix.length + 8),
    Function.iterate_succ_apply _ (prepareSteps n m v rank rs querySuffix),
    advance_some, initializeStep, hp]
  exact hs

theorem prefixTime_le (v : Nat) (rs : List Row) :
    prefixTime v rs ≤ 6 * (encodeWords (rs.flatMap rowWords)).length := by
  induction rs with
  | nil => simp [prefixTime, encodeWords]
  | cons r rs ih =>
    have hr := MachineCloudCount.rowTime_le v r
    have hpos : 1 ≤ (encodeWords (rowWords r)).length := by
      simp only [rowWords, encodeWords, List.length_append, encodeWord_length]
      omega
    simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.length_append]
    omega

theorem totalSteps_le (n m v rank : Nat) (rs preceding : List Row) (work querySuffix : List Bool)
    (hword : encodeWords (rs.flatMap rowWords) =
      encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work)) :
    totalSteps n m v rank rs preceding work querySuffix ≤
      10 * ((MachineCloudCount.inputWord n m rs).length + (queryWord v rank querySuffix).length) + 20 := by
  have hp := prefixTime_le v preceding
  have hw := congrArg List.length hword
  simp only [List.length_append, encodeWord_length] at hw
  have ht := MachineCloudCount.inputWord_length n m rs
  have hq : (queryWord v rank querySuffix).length =
      v + 1 + (rank + 1) + querySuffix.length := by
    simp only [queryWord, MachineCloudRank.queryWord, List.length_append, encodeWord_length]
    omega
  unfold totalSteps prepareSteps
  omega

open IndependentSetsGames.Foundations.PCP

def remainder (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  encodeWords (t.rows[e].reverseIndex.val :: GraphTables.relationWords t.rows[e].relation) ++
    encodeWords (((tableRows t).drop (e.val + 1)).flatMap rowWords)

theorem tableRows_getElem (t : GraphTables.Table) (e : Fin t.darts) :
    (tableRows t)[e.val]'(by rw [MachineCloudRank.tableRows_length]; exact e.isLt) =
      (t.rows[e].tail.val, t.rows[e].reverseIndex.val :: GraphTables.relationWords t.rows[e].relation) := by
  simp only [MachineCloudCount.tableRows, MachineCloudCount.rowList_eq_finRange_map,
    List.getElem_map, List.getElem_finRange]
  apply congrArg (fun j : Fin t.darts =>
    (t.rows[j].tail.val, t.rows[j].reverseIndex.val :: GraphTables.relationWords t.rows[j].relation))
  apply Fin.ext
  rfl

theorem tableWord_split (t : GraphTables.Table) (v : Fin t.vertices) (e : Fin t.darts)
    (owner : t.rows[e].tail = v) :
    encodeWords ((tableRows t).flatMap rowWords) =
      encodeWords (((tableRows t).take e.val).flatMap rowWords) ++
        (encodeWord v.val ++ remainder t e) := by
  have he : e.val < (tableRows t).length := by
    rw [MachineCloudRank.tableRows_length]
    exact e.isLt
  rw [MachineCloudRank.encoded_rows_split (tableRows t) e.val, List.drop_eq_getElem_cons he]
  simp only [List.flatMap_cons, encodeWords_append]
  rw [tableRows_getElem]
  simp only [rowWords, encodeWords, owner, remainder, List.append_assoc]

def cloudSelectSteps (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix : List Bool) : Nat :=
  let e := (PreprocessingCloudIndex.cloudSelect t v i).val
  totalSteps t.vertices t.darts v.val i.val (tableRows t) ((tableRows t).take e.val)
    (remainder t e) querySuffix

theorem cloudSelectTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[cloudSelectSteps t v i querySuffix]
      (some (cfg (some (.inr .initialize)) .checking (GraphTables.tableBits t)
        [] (queryWord v.val i.val querySuffix) [] [] outputSuffix ambient register)) =
      some (cfg none .checking (GraphTables.tableBits t) [] (queryWord v.val i.val querySuffix)
        [] [] (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val ++ outputSuffix)
        ambient none) := by
  let e := PreprocessingCloudIndex.cloudSelect t v i
  have hword := tableWord_split t v e.val e.property
  have hrank : i.val = rowsHits v.val ((tableRows t).take e.val.val) := by
    simpa only [PreprocessingCloudIndex.cloudRank_cloudSelect] using
      MachineCloudRank.cloudRank_eq_prefix_count t v (PreprocessingCloudIndex.cloudSelect t v i)
  have h := fullTrace t.vertices t.darts v.val i.val (tableRows t)
    ((tableRows t).take e.val.val) (remainder t e.val)
    (by intro r hr; exact MachineCloudCount.tableRows_width t r (List.mem_of_mem_take hr))
    hword hrank querySuffix outputSuffix ambient register
  have htake : ((tableRows t).take e.val.val).length = e.val.val := by
    rw [List.length_take, MachineCloudRank.tableRows_length,
      Nat.min_eq_left e.val.isLt.le]
  rw [MachineCloudCount.tableRows_input, htake] at h
  exact h

theorem cloudSelectSteps_le (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix : List Bool) :
    cloudSelectSteps t v i querySuffix ≤
      10 * ((GraphTables.tableBits t).length + (queryWord v.val i.val querySuffix).length) + 20 := by
  let e := PreprocessingCloudIndex.cloudSelect t v i
  have h := totalSteps_le t.vertices t.darts v.val i.val (tableRows t)
    ((tableRows t).take e.val.val) (remainder t e.val) querySuffix
    (tableWord_split t v e.val e.property)
  simpa only [cloudSelectSteps, e, MachineCloudCount.tableRows_input] using h

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 10 * Polynomial.X + Polynomial.C 20

def cloudSelectInTime (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (cfg (some (.inr .initialize)) .checking (GraphTables.tableBits t)
        [] (queryWord v.val i.val querySuffix) [] [] outputSuffix ambient register)
      (some (cfg none .checking (GraphTables.tableBits t) [] (queryWord v.val i.val querySuffix)
        [] [] (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val ++ outputSuffix)
        ambient none))
      (timePolynomial.eval ((GraphTables.tableBits t).length + (queryWord v.val i.val querySuffix).length)) where
  steps := cloudSelectSteps t v i querySuffix
  evals_in_steps := cloudSelectTrace t v i querySuffix outputSuffix ambient register
  steps_le_m := by
    simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using cloudSelectSteps_le t v i querySuffix

def machine : FinTM2 where
  K := Tape
  k₀ := .inl .original
  k₁ := .inr ()
  Γ := Alphabet
  Λ := Label
  main := .inr .initialize
  σ := State Unit
  initialState := ((((), false), none), .checking)
  m := program

def machineInTime (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix outputSuffix : List Bool)
    (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.inr .initialize)) .checking (GraphTables.tableBits t)
        [] (queryWord v.val i.val querySuffix) [] [] outputSuffix () register)
      (some (cfg none .checking (GraphTables.tableBits t) [] (queryWord v.val i.val querySuffix)
        [] [] (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val ++ outputSuffix)
        () none))
      (timePolynomial.eval ((GraphTables.tableBits t).length + (queryWord v.val i.val querySuffix).length)) where
  steps := cloudSelectSteps t v i querySuffix
  evals_in_steps := by
    convert cloudSelectTrace t v i querySuffix outputSuffix () register using 1
    rfl
  steps_le_m := by
    simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using cloudSelectSteps_le t v i querySuffix

end IndependentSetsGames.Foundations.Complexity.MachineCloudSelect

end OAI
