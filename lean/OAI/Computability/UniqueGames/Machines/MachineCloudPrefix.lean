import OAI.Computability.UniqueGames.Machines.MachineCloudPadding
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineUnaryAddAt
import OAI.Computability.UniqueGames.PCP.PreprocessingPaddingOffsets

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP
open scoped BigOperators

inductive Tape
  | inner (k : MachineCloudPadding.Tape)
  | bound | remaining | total
  deriving DecidableEq, Fintype

inductive Label
  | init | copyFirst | copySecond | guard | done
  | padding (l : MachineCloudPadding.Label)
  | add | clearCount | clearLevel | increment
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (inner : MachineCloudPadding.Tape → List Bool) (bound remaining total : List Bool) :
    Tape → List Bool
  | .inner k => inner k
  | .bound => bound
  | .remaining => remaining
  | .total => total

def frame (table query count power level bound remaining total : List Bool) : Tape → List Bool :=
  memory (MachineCloudPadding.memory table query count [] [] [] power level [] []) bound remaining total

@[simp] theorem frame_query (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .query) = b := rfl
@[simp] theorem frame_count (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .count) = c := rfl
@[simp] theorem frame_power (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .power) = d := rfl
@[simp] theorem frame_level (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .level) = e := rfl
@[simp] theorem frame_bound (a b c d e f g h : List Bool) :
    frame a b c d e f g h .bound = f := rfl
@[simp] theorem frame_remaining (a b c d e f g h : List Bool) :
    frame a b c d e f g h .remaining = g := rfl
@[simp] theorem frame_total (a b c d e f g h : List Bool) :
    frame a b c d e f g h .total = h := rfl

@[simp] theorem update_frame_query (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .query) x =
      frame a x c d e f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_count (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .count) x =
      frame a b x d e f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_power (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .power) x =
      frame a b c x e f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_level (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .level) x =
      frame a b c d x f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_remaining (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) .remaining x =
      frame a b c d e f x h := by
  funext k; cases k <;> rfl
@[simp] theorem update_frame_total (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) .total x =
      frame a b c d e f g x := by
  funext k; cases k <;> rfl

def paddingView : Tape → Option MachineCloudPadding.Tape
  | .inner k => some k
  | _ => none

theorem paddingView_left (k : MachineCloudPadding.Tape) : paddingView (.inner k) = some k := rfl

theorem paddingView_right (j : Tape) (k : MachineCloudPadding.Tape)
    (h : paddingView j = some k) : Tape.inner k = j := by
  cases j <;> simp_all [paddingView]

theorem placedTapes (inner : MachineCloudPadding.Tape → List Bool) (extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes paddingView inner extra =
      memory inner (extra .bound) (extra .remaining) (extra .total) := by
  funext j; cases j <;> rfl

variable {σ : Type}

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push (.inner .query) (fun _ => false)
      (.push .total (fun _ => false) (.goto fun _ => .copyFirst))
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .bound (.inner .scratch) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      (.inner .scratch) .bound .remaining false .copySecond (some .guard)
  | .guard => MachineUnaryCounter.guard .remaining (.padding .init) .done
  | .done => .halt
  | .padding l => MachineCloudPadding.Placement.statement Tape.inner Label.padding (some .add) (MachineCloudPadding.program l)
  | .add => MachineUnaryAddAt.loop (.inner .power) .total .add (some .clearCount)
  | .clearCount => MachineLookup.discard (.inner .count) .clearCount .clearLevel
  | .clearLevel => MachineLookup.discard (.inner .level) .clearLevel .increment
  | .increment => .pop (.inner .power) (fun state _ => (state.1, none))
      (.push (.inner .query) (fun _ => true) (.goto fun _ => .guard))

private theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

/-- The inner program is embedded with its actual table scan and geometric
search; all three additional tapes are preserved by every inner transition. -/
theorem paddingTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (bound remaining total : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudPadding.totalTime t v]
      (some ⟨some (.padding .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] [] [] bound remaining total⟩) =
      some ⟨some .add, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord v.val)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v))
          (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v)))
          (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))
          bound remaining total⟩ := by
  have h := MachineCloudPadding.Placement.trace Tape.inner paddingView paddingView_left paddingView_right
    Label.padding (some Label.add) (frame [] [] [] [] [] bound remaining total)
    (MachineCloudPadding.program (σ := σ)) program (fun _ => rfl) _ _ _
    (MachineCloudPadding.cloudPaddingTrace t v [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label, placedTapes,
    frame_bound, frame_remaining, frame_total, List.append_nil, frame, memory] using h

theorem incrementStep (table bound remaining total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .increment, ((ambient, false), register),
        frame table (encodeWord v) [] (encodeWord 0) [] bound remaining total⟩ =
      some ⟨some .guard, ((ambient, false), none),
        frame table (encodeWord (v + 1)) [] [] [] bound remaining total⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord, List.replicate_succ]

def bodyTime (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPadding.totalTime t v + (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) + 1) +
    (PreprocessingCloudIndex.cloudSize t v + 1) +
      (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v) + 1) + 1

/-- Padding tallies are consumed by unary addition; count and level fields
are scanned away, and the remaining zero padding delimiter is removed while
the physical vertex counter increases. -/
theorem bodyTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (bound remaining : List Bool) (acc : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[bodyTime t v]
      (some ⟨some (.padding .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] [] []
          bound remaining (encodeWord acc)⟩) =
      some ⟨some .guard, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v.val + 1)) [] [] []
          bound remaining (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) + acc))⟩ := by
  let k := PreprocessingCloudIndex.cloudSize t v
  let p := MachineCloudPadding.padding k
  let l := PreprocessingLevels.boundedLevel k
  have hp := paddingTrace t v bound remaining (encodeWord acc) ambient register
  have ha := MachineUnaryAddAt.addFromTapes (Tape.inner .power) Tape.total (by decide)
    Label.add (some Label.clearCount) program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) (encodeWord k)
      (encodeWord p) (encodeWord l) bound remaining (encodeWord acc))
    p acc [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_power, update_frame_total] at ha
  have hc := MachineLookup.discardTrace (Tape.inner .count) Label.clearCount Label.clearLevel
    program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) (encodeWord k)
      (encodeWord 0) (encodeWord l) bound remaining (encodeWord (p + acc)))
    k [] (by simp) (ambient, false) none
  simp only [update_frame_count] at hc
  have hl := MachineLookup.discardTrace (Tape.inner .level) Label.clearLevel Label.increment
    program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) []
      (encodeWord 0) (encodeWord l) bound remaining (encodeWord (p + acc)))
    l [] (by simp) (ambient, false) none
  simp only [update_frame_level] at hl
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .increment, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] (encodeWord 0) []
          bound remaining (encodeWord (p + acc))⟩) =
      some ⟨some .guard, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v.val + 1)) [] [] []
          bound remaining (encodeWord (p + acc))⟩ :=
    incrementStep _ _ _ _ _ ambient none
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hp ha) hc) hl) hi

theorem guardStep_succ (table bound suffix total : List Bool) (v n : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord (n + 1) ++ suffix) total⟩ =
      some ⟨some (.padding .init), ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord n ++ suffix) total⟩ := by
  simp [TM2.step, program, MachineUnaryCounter.guard, TM2.stepAux, encodeWord,
    List.replicate_succ]

theorem guardStep_zero (table bound suffix total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ =
      some ⟨some .done, ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ := rfl

theorem zeroTrace (table bound suffix total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[2]
      (some ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩) =
      some ⟨none, ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ := by
  rw [Function.iterate_succ_apply]
  change advance (TM2.step (program (σ := σ)))
    (TM2.step program ⟨some .guard, ((ambient, false), register),
      frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩) = _
  rw [guardStep_zero]
  rfl

def amount (t : GraphTables.Table) (v : Nat) : Nat :=
  if h : v < t.vertices then MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t ⟨v, h⟩) else 0

def cycleTime (t : GraphTables.Table) (v : Nat) : Nat :=
  if h : v < t.vertices then 1 + bodyTime t ⟨v, h⟩ else 0

def sumFrom (t : GraphTables.Table) (v : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => amount t v + sumFrom t (v + 1) n

def loopTime (t : GraphTables.Table) (v : Nat) : Nat → Nat
  | 0 => 2
  | n + 1 => cycleTime t v + loopTime t (v + 1) n

theorem loopTrace (t : GraphTables.Table) (n v : Nat) (hvn : v + n ≤ t.vertices)
    (bound suffix : List Bool) (acc : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[loopTime t v n]
      (some ⟨some .guard, ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v) [] [] []
          bound (encodeWord n ++ suffix) (encodeWord acc)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v + n)) [] [] []
          bound (encodeWord 0 ++ suffix) (encodeWord (sumFrom t v n + acc))⟩ := by
  induction n generalizing v acc register with
  | zero =>
      simpa only [loopTime, sumFrom, Nat.add_zero, Nat.zero_add] using
        zeroTrace _ bound suffix (encodeWord acc) v ambient register
  | succ n ih =>
      have hv : v < t.vertices := by omega
      have hnext : v + 1 + n ≤ t.vertices := by omega
      have hg : (advance (TM2.step program))^[1]
          (some ⟨some .guard, ((ambient, false), register),
            frame (GraphTables.tableBits t) (encodeWord v) [] [] []
              bound (encodeWord (n + 1) ++ suffix) (encodeWord acc)⟩) =
          some ⟨some (.padding .init), ((ambient, false), none),
            frame (GraphTables.tableBits t) (encodeWord v) [] [] []
              bound (encodeWord n ++ suffix) (encodeWord acc)⟩ :=
        guardStep_succ _ bound suffix (encodeWord acc) v n ambient register
      have hb := bodyTrace t ⟨v, hv⟩ bound (encodeWord n ++ suffix) acc ambient none
      have ht := ih (v + 1) hnext
        (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t ⟨v, hv⟩) + acc) none
      have hall := appendTrace _ (appendTrace _ hg hb) ht
      simpa only [loopTime, cycleTime, dite_eq_left hv, sumFrom, amount,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem sumFrom_list (t : GraphTables.Table) (xs : List (Fin t.vertices)) (v : Nat)
    (hseq : ∀ i (hi : i < xs.length), (xs[i]).val = v + i) :
    sumFrom t v xs.length = (xs.map (PreprocessingRegularTables.padding t)).sum := by
  induction xs generalizing v with
  | nil => simp [sumFrom]
  | cons x xs ih =>
      have hx : x.val = v := by simpa using! hseq 0 (by simp)
      have hv : v < t.vertices := by simpa only [hx] using x.isLt
      have he : (⟨v, hv⟩ : Fin t.vertices) = x := Fin.ext hx.symm
      have hnext : ∀ i (hi : i < xs.length), (xs[i]).val = v + 1 + i := by
        intro i hi
        have h := hseq (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      simp only [List.length_cons, sumFrom, amount, dite_eq_left hv, he,
        List.map_cons, List.sum_cons]
      rw [ih (v + 1) hnext]
      rfl

theorem sumFrom_eq_offset (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices) :
    sumFrom t 0 b =
      PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) b := by
  have h := sumFrom_list t ((List.finRange t.vertices).take b) 0
    (by intro i hi; simp only [List.getElem_take, List.getElem_finRange, Fin.val_cast,
      Nat.zero_add])
  simpa only [List.length_take, List.length_finRange, Nat.min_eq_left hb,
    PreprocessingPaddingOffsets.offset] using h

theorem initStep (table bound : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .init, ((ambient, false), register), frame table [] [] [] [] bound [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame table (encodeWord 0) [] [] [] bound [] (encodeWord 0)⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def totalTime (t : GraphTables.Table) (b : Nat) (suffix : List Bool) : Nat :=
  (1 + 2 * ((encodeWord b ++ suffix).length + 1)) + loopTime t 0 b

theorem prefixTrace (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t b suffix]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord b) [] [] []
          (encodeWord b ++ suffix) (encodeWord 0 ++ suffix)
          (encodeWord (PreprocessingPaddingOffsets.offset
            (PreprocessingRegularTables.padding t) b))⟩ := by
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord 0) [] [] []
          (encodeWord b ++ suffix) [] (encodeWord 0)⟩ :=
    initStep _ _ ambient register
  have hc := MachineCopy.copyTrace Tape.bound Tape.remaining (Tape.inner .scratch)
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.guard) program rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord 0) [] [] []
      (encodeWord b ++ suffix) [] (encodeWord 0)) rfl (ambient, false) register
  simp only [frame_bound, frame_remaining, List.append_nil, update_frame_remaining] at hc
  have hl := loopTrace t b 0 (by simpa only [Nat.zero_add] using hb)
    (encodeWord b ++ suffix) suffix 0 ambient none
  simp only [Nat.zero_add, Nat.add_zero, sumFrom_eq_offset t b hb] at hl
  exact appendTrace _ (appendTrace _ hi hc) hl

/-- Uniform budget for one vertex iteration, including unary addition and
cleanup. Its input argument bounds the complete table length. -/
def cycleBudget (L : Nat) : Nat :=
  (ExpanderFamily.growth + 8) * (2 * L) ^ 2 + 25 * (2 * L) + 10 +
    (ExpanderFamily.growth + 2) * L + 5

theorem bodyTime_le (t : GraphTables.Table) (v : Fin t.vertices) (L : Nat)
    (hL : (GraphTables.tableBits t).length ≤ L) :
    1 + bodyTime t v ≤ cycleBudget L := by
  have hn := GraphTables.vertices_le_tableBits_length t
  have hv := v.isLt
  have hinput : MachineCloudPadding.inputLength t v [] ≤ 2 * L := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hinput)
  simp only [MachineCloudPadding.timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at hp
  have hk : PreprocessingCloudIndex.cloudSize t v ≤ L :=
    (PreprocessingCloudIndex.cloudSize_le_darts t v).trans
      ((GraphTables.darts_le_tableBits_length t).trans hL)
  have hl := (PreprocessingLevels.boundedLevel_le_input
    (PreprocessingCloudIndex.cloudSize t v)).trans hk
  have hpad : MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) ≤
      ExpanderFamily.growth * L := by
    have hsize := (PreprocessingLevels.cloudPaddedSize_bounds
      (PreprocessingCloudIndex.cloudSize t v)).2
    have hmul := Nat.mul_le_mul_left ExpanderFamily.growth hk
    unfold MachineCloudPadding.padding
    omega
  unfold bodyTime cycleBudget
  simp only [Nat.add_mul] at hp ⊢
  omega

theorem loopTime_le (t : GraphTables.Table) (n v : Nat) (hvn : v + n ≤ t.vertices)
    (L : Nat) (hL : (GraphTables.tableBits t).length ≤ L) :
    loopTime t v n ≤ n * cycleBudget L + 2 := by
  induction n generalizing v with
  | zero => simp only [loopTime, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ n ih =>
      have hv : v < t.vertices := by omega
      have hnext : v + 1 + n ≤ t.vertices := by omega
      have hbody := bodyTime_le t ⟨v, hv⟩ L hL
      have htail := ih (v + 1) hnext
      simp only [loopTime, cycleTime, dite_eq_left hv, Nat.succ_mul]
      omega

def inputLength (t : GraphTables.Table) (b : Nat) (suffix : List Bool) : Nat :=
  (GraphTables.tableBits t).length + (encodeWord b ++ suffix).length

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X *
      (Polynomial.C (ExpanderFamily.growth + 8) * (2 * Polynomial.X) ^ 2 +
        25 * (2 * Polynomial.X) + 10 +
          Polynomial.C (ExpanderFamily.growth + 2) * Polynomial.X + 5) +
    2 * (Polynomial.X + 1) + 3

/-- The full execution has a cubic polynomial bound in the two actual
preserved input words. The accumulator is never scanned to perform addition. -/
theorem totalTime_le (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices)
    (suffix : List Bool) :
    totalTime t b suffix ≤ timePolynomial.eval (inputLength t b suffix) := by
  let L := inputLength t b suffix
  have htable : (GraphTables.tableBits t).length ≤ L := by
    unfold L inputLength
    omega
  have hbound : (encodeWord b ++ suffix).length ≤ L := by
    unfold L inputLength
    omega
  have hbL : b ≤ L := hb.trans ((GraphTables.vertices_le_tableBits_length t).trans htable)
  have hloop := loopTime_le t b 0 (by simpa only [Nat.zero_add] using hb) L htable
  have hmul := Nat.mul_le_mul_right (cycleBudget L) hbL
  have htotal : totalTime t b suffix ≤ L * cycleBudget L + 2 * (L + 1) + 3 := by
    unfold totalTime
    omega
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one, cycleBudget, L] using htotal

def prefixInTime (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩
      (some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord b) [] [] []
          (encodeWord b ++ suffix) (encodeWord 0 ++ suffix)
          (encodeWord (PreprocessingPaddingOffsets.offset
            (PreprocessingRegularTables.padding t) b))⟩)
      (timePolynomial.eval (inputLength t b suffix)) where
  steps := totalTime t b suffix
  evals_in_steps := prefixTrace t b hb suffix ambient register
  steps_le_m := totalTime_le t b hb suffix

/-- At the complete vertex bound the output is the sum of all padding
counts used by the actual regularized-table header. -/
theorem all_padding_sum (t : GraphTables.Table) :
    sumFrom t 0 t.vertices = ∑ v, PreprocessingRegularTables.padding t v := by
  rw [sumFrom_eq_offset t t.vertices (Nat.le_refl _), PreprocessingPaddingOffsets.offset_all]

/-- At a vertex bound, adding its local dummy index to this machine's result
gives precisely the existing executable padding-order index. -/
theorem paddingOrder_eq_prefix (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (PreprocessingRegularTables.padding t v)) :
    (PreprocessingRegularTables.paddingOrder (PreprocessingRegularTables.padding t) ⟨v, j⟩).val =
      sumFrom t 0 v.val + j.val := by
  rw [PreprocessingPaddingOffsets.paddingOrder_val,
    sumFrom_eq_offset t v.val v.isLt.le]

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

end OAI
