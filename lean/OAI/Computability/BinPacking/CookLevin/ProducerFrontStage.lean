import OAI.Computability.BinPacking.CookLevin.CellsTokensAlignment
import OAI.Computability.BinPacking.CookLevin.CircuitFinish
import OAI.Computability.BinPacking.CookLevin.TransitionArena
import OAI.Computability.BinPacking.CookLevin.VerifierFront

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Ports (K : Type) := Fin 5 ↪ K

inductive Label
  | copy | restore | seed
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copy, .restore, .seed]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State (σ : Type) := σ × Option Bool

structure Ready (p : Ports K) (base : K → List Bool) (free : Nat) : Prop where
  source : base (p 0) = encodeWord free
  current : base (p 1) = []
  scratch : base (p 2) = []
  count : base (p 3) = []
  cursor : base (p 4) = []

def copied (p : Ports K) (base : K → List Bool) : K → List Bool :=
  Function.update base (p 1) (base (p 0) ++ base (p 1))

def prepared (p : Ports K) (base : K → List Bool) : K → List Bool :=
  Function.update (Function.update (copied p base) (p 3) (false :: copied p base (p 3)))
    (p 4) (false :: copied p base (p 4))

def statement (p : Ports K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (State σ)
  | .copy => Reduction.MachineTransfer.loopAt (p 0) (p 2) id false
      (labels .copy) (some (labels .restore))
  | .restore => MachineCopy.forkLoop (p 2) (p 0) (p 1) false
      (labels .restore) (some (labels .seed))
  | .seed => .push (p 3) (fun _ => false)
      (.push (p 4) (fun _ => false) (Reduction.MachineTransfer.exitAt (p 4) exit))

theorem prepared_current (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 1) = encodeWord free := by
  simp [prepared, copied, p.injective.eq_iff, ready.source, ready.current]

theorem prepared_source (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 0) = encodeWord free := by
  simp [prepared, copied, p.injective.eq_iff, ready.source]

theorem prepared_count (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 3) = encodeWord 0 := by
  simp [prepared, copied, p.injective.eq_iff, ready.count, encodeWord]

theorem prepared_cursor (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 4) = encodeWord 0 := by
  simp [prepared, copied, p.injective.eq_iff, ready.cursor, encodeWord]

theorem prepared_scratch (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 2) = [] := by
  simp [prepared, copied, p.injective.eq_iff, ready.scratch]

theorem prepared_other (p : Ports K) (base : K → List Bool) (k : K)
    (hc : k ≠ p 1) (ht : k ≠ p 3) (hz : k ≠ p 4) : prepared p base k = base k := by
  simp [prepared, copied, hc, ht, hz]

theorem seedTrace (p : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : program (labels .seed) = statement p labels exit .seed)
    (base : K → List Bool) (ambient : σ) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .seed), (ambient, none), copied p base⟩) =
      some ⟨exit, (ambient, none), prepared p base⟩ := by
  change some (TM2.stepAux (program (labels .seed)) _ _) = _
  rw [code]
  cases exit <;>
    simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt, prepared,
      p.injective.eq_iff]

theorem trace (p : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, program (labels l) = statement p labels exit l)
    (base : K → List Bool) (free : Nat) (ready : Ready p base free)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * free + 5]
      (some ⟨some (labels .copy), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), prepared p base⟩ := by
  have hc := MachineCopy.copyTrace (p 0) (p 1) (p 2)
    (p.injective.ne (by decide : (0 : Fin 5) ≠ 1))
    (p.injective.ne (by decide : (0 : Fin 5) ≠ 2))
    (p.injective.ne (by decide : (1 : Fin 5) ≠ 2))
    false (labels .copy) (labels .restore) (some (labels .seed))
    program (code .copy) (code .restore) base ready.scratch ambient register
  have hs := seedTrace p labels exit program (code .seed) base ambient
  have time : 2 * free + 5 = 1 + 2 * ((base (p 0)).length + 1) := by
    rw [ready.source, encodeWord_length]
    omega
  rw [time, Function.iterate_add_apply, hc]
  exact hs

def inTime (p : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, program (labels l) = statement p labels exit l)
    (base : K → List Bool) (free : Nat) (ready : Ready p base free)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copy), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), prepared p base⟩) (2 * free + 5) where
  steps := 2 * free + 5
  evals_in_steps := by
    change (advance (TM2.step program))^[2 * free + 5] _ = _
    exact trace p labels exit program code base free ready ambient register
  steps_le_m := le_rfl

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

namespace BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine

open Turing MachineComposition PostfixModel
open ClashMachine (State clean emitted emitted_append chain)
open PayloadCellsMachine (SymbolSpec)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev Ports (K : Type) := Fin 14 ↪ K
abbrev Alphabet (_ : K) := Bool

def prefixMap : Fin 7 ↪ Fin 14 := ⟨![0, 2, 3, 4, 5, 6, 7], by decide⟩
def loopMap : Fin 11 ↪ Fin 14 := ⟨![1, 8, 9, 10, 11, 7, 12, 3, 4, 13, 6], by decide⟩
def paddingMap : Fin 4 ↪ Fin 14 := ⟨![5, 3, 4, 6], by decide⟩

abbrev prefixPorts (p : Ports K) := prefixMap.trans p
abbrev loopPorts (p : Ports K) := loopMap.trans p
abbrev paddingPorts (p : Ports K) := paddingMap.trans p

def WorkEmpty (p : Ports K) (base : K → List Bool) : Prop :=
  ∀ j : Fin 14, 5 ≤ j.val → base (p j) = []

structure Ready (p : Ports K) (base : K → List Bool) (input : List Bool) (q S : Nat) : Prop where
  inputWord : base (p 0) = input
  boundWord : base (p 1) = encodeWord q
  capacityWord : base (p 2) = encodeWord S
  empty : WorkEmpty p base

theorem workEmpty_emitted (p : Ports K) (base : K → List Bool) (tokens : List Token)
    (h : WorkEmpty p base) : WorkEmpty p (emitted (p 3) (p 4) base tokens) := by
  intro j hj
  have h3 : j ≠ 3 := by intro h; subst j; norm_num at hj
  have h4 : j ≠ 4 := by intro h; subst j; norm_num at hj
  simpa [emitted, p.injective.eq_iff, h3, h4] using h j hj

abbrev frame (p : Ports K) (base : K → List Bool) (m i c : Nat) :=
  PayloadRowsLoop.frame (loopPorts p) base m i c

private theorem ext_ports (p : Ports K) {f g : K → List Bool}
    (atPorts : ∀ j, f (p j) = g (p j))
    (outside : ∀ k, (∀ j, k ≠ p j) → f k = g k) : f = g := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    exact atPorts j
  · exact outside k (fun j h => hk ⟨j, h.symm⟩)

theorem frame_emitted (p : Ports K) (base : K → List Bool) (m i c : Nat) (ts : List Token) :
    emitted (p 3) (p 4) (frame p base m i c) ts =
      frame p (emitted (p 3) (p 4) base ts) m i c :=
  PayloadRowsLoop.frame_emitted (loopPorts p) base m i c ts

theorem update_emitted_capacity (p : Ports K) (base : K → List Bool) (c : Nat) (ts : List Token) :
    emitted (p 3) (p 4) (Function.update base (p 6) (encodeWord c)) ts =
      Function.update (emitted (p 3) (p 4) base ts) (p 6) (encodeWord c) := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [emitted, p.injective.eq_iff]
  · intro k hk
    simp [emitted, hk]

theorem frame_seed (p : Ports K) (base : K → List Bool) (m i c : Nat) :
    frame p (Function.update base (p 8) (encodeWord 0)) m i c = frame p base m i c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, PayloadRowsLoop.frame, loopPorts, loopMap, p.injective.eq_iff]
  · intro k hk
    simp [frame, PayloadRowsLoop.frame, loopPorts, loopMap, hk]

theorem seed_ready (p : Ports K) (base : K → List Bool) (q : Nat)
    (hq : base (p 1) = encodeWord q) (empty : WorkEmpty p base) :
    PayloadPresenceMachine.Ready (PayloadRowsLoop.rowPorts (loopPorts p))
      (Function.update base (p 8) (encodeWord 0)) q 0 := by
  have rowPort (j : Fin 9) : PayloadRowsLoop.rowPorts (loopPorts p) j =
      p (![1, 8, 9, 10, 11, 7, 12, 3, 4] j) := by
    simp only [PayloadRowsLoop.rowPorts, PayloadRowsLoop.rowMap]
    fin_cases j <;> rfl
  constructor
  · simpa [rowPort, p.injective.eq_iff] using hq
  · change Function.update base (p 8) (encodeWord 0) (p 8) = encodeWord 0
    exact Function.update_self _ _ _
  · intro j h0 h1 h7 h8
    fin_cases j <;> try contradiction
    · simpa [rowPort, p.injective.eq_iff] using empty 9 (by decide)
    · simpa [rowPort, p.injective.eq_iff] using empty 10 (by decide)
    · simpa [rowPort, p.injective.eq_iff] using empty 11 (by decide)
    · simpa [rowPort, p.injective.eq_iff] using empty 7 (by decide)
    · simpa [rowPort, p.injective.eq_iff] using empty 12 (by decide)

inductive Label (A : Nat)
  | prefix (entry : CellsPrefixStage.Label A)
  | copyFirst | copySecond | seed
  | payload (entry : PayloadRowsLoop.Label A)
  | padding | cleanup | drain
  deriving DecidableEq, Fintype

def prefixLabels (labels : Label A ↪ Λ) : CellsPrefixStage.Label A ↪ Λ :=
  ⟨fun l => labels (.prefix l), fun _ _ h => Label.prefix.inj (labels.injective h)⟩

def payloadLabels (labels : Label A ↪ Λ) : PayloadRowsLoop.Label A ↪ Λ :=
  ⟨fun l => labels (.payload l), fun _ _ h => Label.payload.inj (labels.injective h)⟩

def statement (p : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (prefixTable : InputCellsMachine.TruthTable A) (payload : Fin A → SymbolSpec) (blank : List Token) :
    Label A → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .prefix l => CellsPrefixStage.statement (prefixPorts p) (prefixLabels labels)
      (some (labels .copyFirst)) prefixTable l
  | .copyFirst => Reduction.MachineTransfer.loopAt (p 1) (p 7) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (p 7) (p 1) (p 13) false
      (labels .copySecond) (some (labels .seed))
  | .seed => .push (p 8) (fun _ => false) (.goto fun _ => labels (.payload .guard))
  | .payload l => PayloadRowsLoop.statement (loopPorts p) (payloadLabels labels)
      (labels .padding) payload l
  | .padding => PaddingCellsMachine.statement (paddingPorts p) blank (labels .padding)
      (some (labels .cleanup))
  | .cleanup => .pop (p 13) (fun s _ => s)
      (.pop (p 6) (fun s _ => s) (.goto fun _ => labels .drain))
  | .drain => MachineDrain.drain (p 8) (labels .drain) exit

def Agrees (p : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (prefixTable : InputCellsMachine.TruthTable A) (payload : Fin A → SymbolSpec) (blank : List Token)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) : Prop :=
  ∀ l, program (labels l) = statement p labels exit prefixTable payload blank l

variable (p : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
  (prefixTable : InputCellsMachine.TruthTable A) (payload : Fin A → SymbolSpec) (blank : List Token)
  (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
  (ha : Agrees p labels exit prefixTable payload blank program)

include ha

theorem prefixTrace (base : K → List Bool) (input : List Bool) (q S : Nat)
    (hS : input.length ≤ S) (ready : Ready p base input q S) (ambient : σ) :
    (advance (TM2.step program))^[2 * (S + 2) + ((A + 4) * input.length + 3)]
      (some ⟨some (labels (.prefix .capacityFirst)), clean ambient, base⟩) =
      some ⟨some (labels .copyFirst), clean ambient,
        Function.update (emitted (p 3) (p 4) base (InputCellsMachine.streamTokens prefixTable input))
          (p 6) (encodeWord (S - input.length))⟩ := by
  have h := CellsPrefixStage.trace (prefixPorts p) (prefixLabels labels)
    (some (labels .copyFirst)) prefixTable program (fun l => ha (.prefix l)) base input S hS
    ready.inputWord ready.capacityWord (ready.empty 5 (by decide))
    (ready.empty 6 (by decide)) (ready.empty 7 (by decide)) (ambient, false) none
  have ht : InputCellsCapacity.tapes (CellsPrefixStage.capacityPorts (prefixPorts p)) base
      (S - input.length) []
      ((tokenBits (InputCellsMachine.streamTokens prefixTable input)).reverse ++ base (p 3))
      (List.replicate (A * input.length) true ++ base (p 4)) =
      Function.update (emitted (p 3) (p 4) base (InputCellsMachine.streamTokens prefixTable input))
        (p 6) (encodeWord (S - input.length)) := by
    simp only [InputCellsCapacity.tapes, InputCellsCapacity.corePorts,
      CellsPrefixStage.capacityPorts, prefixPorts, prefixMap]
    change Function.update (Function.update (Function.update
      (Function.update base (p 6) (encodeWord (S - input.length))) (p 5) [])
        (p 3) ((tokenBits (InputCellsMachine.streamTokens prefixTable input)).reverse ++ base (p 3)))
      (p 4) (List.replicate (A * input.length) true ++ base (p 4)) = _
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [emitted, p.injective.eq_iff, ready.empty 5 (by decide)]
    · intro k hk
      simp [emitted, hk]
  rw [show prefixPorts p 2 = p 3 from rfl, show prefixPorts p 3 = p 4 from rfl, ht] at h
  exact h

theorem preparePayloadTrace (base : K → List Bool) (q c : Nat)
    (hq : base (p 1) = encodeWord q) (empty : WorkEmpty p base) (ambient : σ) :
    (advance (TM2.step program))^[2 * (q + 2) + 1]
      (some ⟨some (labels .copyFirst), clean ambient,
        Function.update base (p 6) (encodeWord c)⟩) =
      some ⟨some (labels (.payload .guard)), clean ambient, frame p base q 0 c⟩ := by
  let start := Function.update base (p 6) (encodeWord c)
  have hc := MachineCopy.copyTrace (p 1) (p 13) (p 7)
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))
    false (labels .copyFirst) (labels .copySecond) (some (labels .seed)) program
    (ha .copyFirst) (ha .copySecond) start
    (by simpa [start, p.injective.eq_iff] using empty 7 (by decide)) (ambient, false) none
  have hs : start (p 1) = encodeWord q := by simpa [start, p.injective.eq_iff] using hq
  have he : start (p 13) = [] := by simpa [start, p.injective.eq_iff] using empty 13 (by decide)
  rw [hs, he, List.append_nil, encodeWord_length] at hc
  have hseed : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seed), clean ambient,
        Function.update start (p 13) (encodeWord q)⟩) =
      some ⟨some (labels (.payload .guard)), clean ambient, frame p base q 0 c⟩ := by
    change some (TM2.stepAux (program (labels .seed)) _ _) = _
    rw [ha .seed]
    simp only [statement, TM2.stepAux]
    congr 1
    apply congrArg (fun tapes => (⟨some (labels (.payload .guard)), clean ambient, tapes⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ)))
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [start, frame, PayloadRowsLoop.frame, loopPorts, loopMap,
        p.injective.eq_iff, empty 8 (by decide), encodeWord]
    · intro k hk
      simp [start, frame, PayloadRowsLoop.frame, loopPorts, loopMap, hk]
  exact chain hc hseed

theorem payloadTrace (base : K → List Bool) (q c : Nat)
    (hq : base (p 1) = encodeWord q) (empty : WorkEmpty p base) (ambient : σ) :
    (advance (TM2.step program))^[PayloadRowsLoop.steps payload q 0 q]
      (some ⟨some (labels (.payload .guard)), clean ambient, frame p base q 0 (c + q)⟩) =
      some ⟨some (labels .padding), clean ambient,
        frame p (emitted (p 3) (p 4) base (PayloadRowsLoop.tokens payload q 0 q)) 0 q c⟩ := by
  have h := PayloadRowsLoop.trace (loopPorts p) (payloadLabels labels) (labels .padding)
    payload program (fun l => ha (.payload l)) (Function.update base (p 8) (encodeWord 0))
    q 0 q c (by omega) (seed_ready p base q hq empty) ambient
  change (advance (TM2.step program))^[PayloadRowsLoop.steps payload q 0 q]
      (some ⟨some (labels (.payload .guard)), clean ambient,
        frame p (Function.update base (p 8) (encodeWord 0)) q 0 (c + q)⟩) =
      some ⟨some (labels .padding), clean ambient,
        emitted (p 3) (p 4) (frame p (Function.update base (p 8) (encodeWord 0)) 0 (0 + q) c)
          (PayloadRowsLoop.tokens payload q 0 q)⟩ at h
  simpa only [frame_seed, Nat.zero_add, frame_emitted] using h

theorem paddingTrace (base : K → List Bool) (q c : Nat) (ambient : σ) :
    (advance (TM2.step program))^[c + 1]
      (some ⟨some (labels .padding), clean ambient, frame p base 0 q c⟩) =
      some ⟨some (labels .cleanup), clean ambient,
        frame p (emitted (p 3) (p 4) base (PaddingCellsMachine.repeatedRows blank c)) 0 q 0⟩ := by
  have h := PaddingCellsMachine.trace (paddingPorts p) blank (labels .padding)
    (some (labels .cleanup)) program (ha .padding) (frame p base 0 q c) c []
    (base (p 3)) (base (p 4)) (ambient, false) none
  have hstart : PaddingCellsMachine.frame (paddingPorts p) (frame p base 0 q c)
      (encodeWord c ++ []) (base (p 3)) (base (p 4)) = frame p base 0 q c := by
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [PaddingCellsMachine.frame, OrClosure.frame,
        PaddingCellsMachine.corePorts, paddingPorts, paddingMap, frame, PayloadRowsLoop.frame,
        loopPorts, loopMap, p.injective.eq_iff]
    · intro k hk
      simp [PaddingCellsMachine.frame, OrClosure.frame, PaddingCellsMachine.corePorts,
        paddingPorts, paddingMap, frame, PayloadRowsLoop.frame, loopPorts, loopMap, hk]
  have hend : PaddingCellsMachine.frame (paddingPorts p) (frame p base 0 q c)
      (encodeWord 0 ++ [])
      ((tokenBits (PaddingCellsMachine.repeatedRows blank c)).reverse ++ base (p 3))
      (List.replicate (c * blank.length) true ++ base (p 4)) =
      frame p (emitted (p 3) (p 4) base (PaddingCellsMachine.repeatedRows blank c)) 0 q 0 := by
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [PaddingCellsMachine.frame, OrClosure.frame,
        PaddingCellsMachine.corePorts, paddingPorts, paddingMap, frame, PayloadRowsLoop.frame,
        loopPorts, loopMap, p.injective.eq_iff, emitted]
    · intro k hk
      simp [PaddingCellsMachine.frame, OrClosure.frame, PaddingCellsMachine.corePorts,
        paddingPorts, paddingMap, frame, PayloadRowsLoop.frame, loopPorts, loopMap, emitted, hk]
  simpa only [hstart, hend, clean] using h

theorem cleanupTrace (base : K → List Bool) (q : Nat) (empty : WorkEmpty p base) (ambient : σ) :
    (advance (TM2.step program))^[1 + (q + 2)]
      (some ⟨some (labels .cleanup), clean ambient, frame p base 0 q 0⟩) =
      some ⟨exit, clean ambient, base⟩ := by
  have hc : (advance (TM2.step program))^[1]
      (some ⟨some (labels .cleanup), clean ambient, frame p base 0 q 0⟩) =
      some ⟨some (labels .drain), clean ambient, Function.update base (p 8) (encodeWord q)⟩ := by
    change some (TM2.stepAux (program (labels .cleanup)) _ _) = _
    rw [ha .cleanup]
    simp only [statement, TM2.stepAux]
    congr 1
    apply congrArg (fun tapes => (⟨some (labels .drain), clean ambient, tapes⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ)))
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [frame, PayloadRowsLoop.frame, loopPorts, loopMap,
        p.injective.eq_iff, encodeWord, empty 6 (by decide), empty 13 (by decide)]
    · intro k hk
      simp [frame, PayloadRowsLoop.frame, loopPorts, loopMap, hk]
  have hd := MachineDrain.drainTrace (p 8) (labels .drain) exit program (ha .drain)
    base (encodeWord q) (ambient, false) none
  rw [encodeWord_length] at hd
  have hb : Function.update base (p 8) [] = base := by
    rw [← empty 8 (by decide), Function.update_eq_self]
  rw [hb] at hd
  exact chain hc hd

omit ha in
def tokens (prefixTable : InputCellsMachine.TruthTable A) (payload : Fin A → SymbolSpec)
    (blank : List Token) (input : List Bool) (q S : Nat) : List Token :=
  InputCellsMachine.streamTokens prefixTable input ++ PayloadRowsLoop.tokens payload q 0 q ++
    PaddingCellsMachine.repeatedRows blank (S - input.length - q)

omit ha in
def steps (payload : Fin A → SymbolSpec) (inputLength q S : Nat) : Nat :=
  (2 * (S + 2) + ((A + 4) * inputLength + 3)) + (2 * (q + 2) + 1) +
    PayloadRowsLoop.steps payload q 0 q + (S - inputLength - q + 1) + (1 + (q + 2))

theorem trace (base : K → List Bool) (input : List Bool) (q S : Nat)
    (hS : input.length + q ≤ S) (ready : Ready p base input q S) (ambient : σ) :
    (advance (TM2.step program))^[steps payload input.length q S]
      (some ⟨some (labels (.prefix .capacityFirst)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (p 3) (p 4) base (tokens prefixTable payload blank input q S)⟩ := by
  let pre := InputCellsMachine.streamTokens prefixTable input
  let mid := PayloadRowsLoop.tokens payload q 0 q
  let post := PaddingCellsMachine.repeatedRows blank (S - input.length - q)
  let b₁ := emitted (p 3) (p 4) base pre
  let b₂ := emitted (p 3) (p 4) b₁ mid
  let b₃ := emitted (p 3) (p 4) b₂ post
  have e₁ : WorkEmpty p b₁ := workEmpty_emitted p base pre ready.empty
  have e₂ : WorkEmpty p b₂ := workEmpty_emitted p b₁ mid e₁
  have e₃ : WorkEmpty p b₃ := workEmpty_emitted p b₂ post e₂
  have q₁ : b₁ (p 1) = encodeWord q := by
    simpa [b₁, emitted, p.injective.eq_iff] using ready.boundWord
  have hp := prefixTrace p labels exit prefixTable payload blank program ha base input q S
    (by omega) ready ambient
  have hprep := preparePayloadTrace p labels exit prefixTable payload blank program ha b₁ q
    (S - input.length) q₁ e₁ ambient
  have hm := payloadTrace p labels exit prefixTable payload blank program ha b₁ q
    (S - input.length - q) q₁ e₁ ambient
  rw [show S - input.length - q + q = S - input.length by omega] at hm
  have hpad := paddingTrace p labels exit prefixTable payload blank program ha b₂ q
    (S - input.length - q) ambient
  have hc := cleanupTrace p labels exit prefixTable payload blank program ha b₃ q e₃ ambient
  have h := chain (chain (chain (chain hp hprep) hm) hpad) hc
  simpa only [steps, b₃, b₂, b₁, pre, mid, post,
    emitted_append (p 3) (p 4) (p.injective.ne (by decide : (3 : Fin 14) ≠ 4)), tokens,
    List.append_assoc] using h

omit ha in
theorem steps_le (payload : Fin A → SymbolSpec) (inputLength q S : Nat) :
    steps payload inputLength q S ≤
      (2 * (S + 2) + ((A + 4) * inputLength + 3)) + (2 * (q + 2) + 1) +
      (q * (A * (120 * (q + 2) ^ 2 + 1) + 3) + 1) + (S + 1) + (q + 3) := by
  have h := PayloadRowsLoop.steps_le payload q 0 q (by omega)
  unfold steps
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssemblyBounds

open Polynomial

local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def cellsPolynomial (V : NPVerifier) : Polynomial Nat :=
  let A := (VerifierCircuit.indexing V).symbolCount
  let q := V.witnessBound
  let s := Bounds.capacityPolynomial V.computation.time q
    (Runtime.programPushBound V.computation.tm)
  (2 * (s + 2) + (C (A + 4) * (2 * X + 1) + 3)) + (2 * (q + 2) + 1) +
    (q * (C A * (120 * (q + 2)^2 + 1) + 3) + 1) + (s + 1) + (q + 3)

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  1 + cellsPolynomial V + ValidityMachine.Full.timePolynomial.comp V.witnessBound

theorem capacityPolynomial_eval (V : NPVerifier) (n : Nat) :
    (Bounds.capacityPolynomial V.computation.time V.witnessBound
      (Runtime.programPushBound V.computation.tm)).eval n = VerifierCircuit.capacity V n := by
  simp [VerifierCircuit.capacity, NPVerifier.horizon, Nat.mul_comm]

theorem cellsPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (cellsPolynomial V).eval input.length =
      (2 * (VerifierCircuit.capacity V input.length + 2) +
        (((VerifierCircuit.indexing V).symbolCount + 4) * (WitnessEncoding.inputPrefix input).length + 3)) +
      (2 * (V.witnessBound.eval input.length + 2) + 1) +
      (V.witnessBound.eval input.length * ((VerifierCircuit.indexing V).symbolCount *
        (120 * (V.witnessBound.eval input.length + 2)^2 + 1) + 3) + 1) +
      (VerifierCircuit.capacity V input.length + 1) + (V.witnessBound.eval input.length + 3) := by
  simp only [cellsPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one, capacityPolynomial_eval, WitnessEncoding.inputPrefix_length]

theorem cells_steps_le (V : NPVerifier) (input : List Bool) :
    CellsMachine.steps (PayloadCellsMachine.symbolTable V) (WitnessEncoding.inputPrefix input).length
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) ≤
      (cellsPolynomial V).eval input.length := by
  rw [cellsPolynomial_eval]
  exact CellsMachine.steps_le (PayloadCellsMachine.symbolTable V)
    (WitnessEncoding.inputPrefix input).length (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length)

theorem steps_le (V : NPVerifier) (input : List Bool) :
    1 + CellsMachine.steps (PayloadCellsMachine.symbolTable V) (WitnessEncoding.inputPrefix input).length
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) +
      ValidityMachine.Full.steps (V.witnessBound.eval input.length) ≤
      (timePolynomial V).eval input.length := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_comp]
  exact Nat.add_le_add (Nat.add_le_add_left (cells_steps_le V input) 1)
    (ValidityMachine.Full.steps_le_time (V.witnessBound.eval input.length))

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssemblyBounds

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly

open Turing PostfixModel

inductive Tape (cellWork : Nat) where
  | rawInput | framedInput | witnessBound | capacity | reversed | count
  | validityWork (index : Fin 7)
  | cellWork (index : Fin cellWork)
  deriving DecidableEq, Fintype

def validitySlots (n : Nat) : Fin 10 ↪ Tape n :=
  ⟨![.witnessBound, .validityWork 0, .validityWork 1, .validityWork 2,
      .validityWork 3, .validityWork 4, .validityWork 5, .reversed, .count,
      .validityWork 6], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

@[simp] private theorem validitySlots_apply (n : Nat) (i : Fin 10) :
    validitySlots n i =
      ![.witnessBound, .validityWork 0, .validityWork 1, .validityWork 2,
        .validityWork 3, .validityWork 4, .validityWork 5, .reversed, .count,
        .validityWork 6] i := by
  simp only [validitySlots]
  rfl

def controlPorts (n : Nat) : InitializationControl.Ports (Tape n) where
  reversed := .reversed
  count := .count
  distinct := by intro h; cases h

theorem validityReady {n : Nat} (base : Tape n → List Bool) (q : Nat)
    (hbound : base .witnessBound = encodeWord q)
    (hwork : ∀ j, base (.validityWork j) = []) :
    ClashMachine.Full.Ready (validitySlots n) base q where
  source := hbound
  empty := by
    intro j hj ho hc
    fin_cases j <;> simp_all

theorem control_emitted_eq {n : Nat} (base : Tape n → List Bool) (ts : List Token) :
    InitializationControl.emitted (controlPorts n) base ts =
      ClashMachine.emitted ((validitySlots n) 7) ((validitySlots n) 8) base ts := rfl

theorem validityReady_control {n : Nat} {base : Tape n → List Bool} {q : Nat}
    (ready : ClashMachine.Full.Ready (validitySlots n) base q) (V : NPVerifier) :
    ClashMachine.Full.Ready (validitySlots n)
      (InitializationControl.emitted (controlPorts n) base (InitializationControl.tokens V)) q := by
  rw [control_emitted_eq]
  exact ready.emitted (InitializationControl.tokens V)

theorem validitySlots_not_cellWork (n : Nat) (i : Fin 10) (j : Fin n) :
    validitySlots n i ≠ Tape.cellWork j := by
  fin_cases i <;> simp

theorem controlTrace {n : Nat} {Λ σ : Type}
    (V : NPVerifier) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : Tape n => Bool) Λ σ)
    (code : program entry = InitializationControl.statement V (controlPorts n) exit)
    (base : Tape n → List Bool) (state : σ) (q : Nat)
    (ready : ClashMachine.Full.Ready (validitySlots n) base q) :
    ((MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some entry, state, base⟩) =
        some ⟨exit, state, InitializationControl.emitted (controlPorts n) base
          (InitializationControl.tokens V)⟩) ∧
      ClashMachine.Full.Ready (validitySlots n)
        (InitializationControl.emitted (controlPorts n) base (InitializationControl.tokens V)) q :=
  ⟨InitializationControl.trace V (controlPorts n) entry exit program code base state,
    validityReady_control ready V⟩

open MachineComposition
open ClashMachine (State clean emitted)

def cellsSlots : Fin 14 ↪ Tape 9 :=
  ⟨![.framedInput, .witnessBound, .capacity, .reversed, .count,
      .cellWork 0, .cellWork 1, .cellWork 2, .cellWork 3, .cellWork 4,
      .cellWork 5, .cellWork 6, .cellWork 7, .cellWork 8], by decide⟩

inductive CodeLabel (A : Nat) where
  | control
  | cells (label : CellsMachine.Label A)
  | validity (label : ValidityMachine.Full.Label)
  deriving DecidableEq, Fintype

abbrev Label (V : NPVerifier) := CodeLabel (VerifierCircuit.indexing V).symbolCount

variable {K Λ σ : Type} [DecidableEq K]

def placedControl (slots : Tape 9 ↪ K) : InitializationControl.Ports K where
  reversed := slots .reversed
  count := slots .count
  distinct := slots.injective.ne (by decide)

def cellsLabels {V : NPVerifier} (labels : Label V ↪ Λ) :
    CellsMachine.Label (VerifierCircuit.indexing V).symbolCount ↪ Λ :=
  ⟨fun l => labels (.cells l), fun _ _ h => CodeLabel.cells.inj (labels.injective h)⟩

structure Ready (V : NPVerifier) (slots : Tape 9 ↪ K) (base : K → List Bool)
    (input : List Bool) : Prop where
  rawWord : base (slots .rawInput) = input
  framedWord : base (slots .framedInput) = WitnessEncoding.inputPrefix input
  boundWord : base (slots .witnessBound) = encodeWord (V.witnessBound.eval input.length)
  capacityWord : base (slots .capacity) = encodeWord (VerifierCircuit.capacity V input.length)
  cellEmpty : ∀ j, base (slots (.cellWork j)) = []
  validityEmpty : ∀ j, base (slots (.validityWork j)) = []

theorem Ready.afterEmitted {V : NPVerifier} {slots : Tape 9 ↪ K}
    {base : K → List Bool} {input : List Bool} (ready : Ready V slots base input)
    (ts : List Token) :
    Ready V slots (emitted (slots .reversed) (slots .count) base ts) input := by
  constructor
  · simpa [emitted, slots.injective.eq_iff] using ready.rawWord
  · simpa [emitted, slots.injective.eq_iff] using ready.framedWord
  · simpa [emitted, slots.injective.eq_iff] using ready.boundWord
  · simpa [emitted, slots.injective.eq_iff] using ready.capacityWord
  · intro j
    simpa [emitted, slots.injective.eq_iff] using ready.cellEmpty j
  · intro j
    simpa [emitted, slots.injective.eq_iff] using ready.validityEmpty j

omit [DecidableEq K] in
theorem Ready.cellsReady {V : NPVerifier} {slots : Tape 9 ↪ K}
    {base : K → List Bool} {input : List Bool} (ready : Ready V slots base input) :
    CellsMachine.Ready (cellsSlots.trans slots) base (WitnessEncoding.inputPrefix input)
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) := by
  constructor
  · exact ready.framedWord
  · exact ready.boundWord
  · exact ready.capacityWord
  · intro j hj
    fin_cases j <;> simp_all [cellsSlots, ready.cellEmpty]

omit [DecidableEq K] in
theorem Ready.validityReady {V : NPVerifier} {slots : Tape 9 ↪ K}
    {base : K → List Bool} {input : List Bool} (ready : Ready V slots base input) :
    ClashMachine.Full.Ready ((validitySlots 9).trans slots) base
      (V.witnessBound.eval input.length) := by
  constructor
  · exact ready.boundWord
  · intro j hj ho hc
    fin_cases j <;> simp_all [ready.validityEmpty]

theorem capacity_within (V : NPVerifier) (input : List Bool) :
    (WitnessEncoding.inputPrefix input).length + V.witnessBound.eval input.length ≤
      VerifierCircuit.capacity V input.length := by
  simp only [WitnessEncoding.inputPrefix_length, VerifierCircuit.capacity]
  omega

def statement (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) : Label V → TM2.Stmt (fun _ : K => Bool) Λ (State σ)
  | .control => InitializationControl.statement V (placedControl slots)
      (some (labels (.cells (.prefix .capacityFirst))))
  | .cells l => CellsMachine.statement (cellsSlots.trans slots) (cellsLabels labels)
      (some (labels (.validity (.nonempty .initialize))))
      (InputCellsMachine.prefixTruth V) (PayloadCellsMachine.symbolTable V)
      (PaddingCellsMachine.blankRow V) l
  | .validity l => ValidityMachine.Full.statement ((validitySlots 9).trans slots)
      (fun l => labels (.validity l)) exit l

def Agrees (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ)) : Prop :=
  ∀ l, program (labels l) = statement V slots labels exit l

def steps (V : NPVerifier) (input : List Bool) : Nat :=
  1 + CellsMachine.steps (PayloadCellsMachine.symbolTable V)
    (WitnessEncoding.inputPrefix input).length (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length) +
    ValidityMachine.Full.steps (V.witnessBound.eval input.length)

theorem cellsTokens_eq (V : NPVerifier) (input : List Bool) :
    CellsMachine.tokens (InputCellsMachine.prefixTruth V) (PayloadCellsMachine.symbolTable V)
      (PaddingCellsMachine.blankRow V) (WitnessEncoding.inputPrefix input)
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) =
      InitializationControl.cells V input (VerifierCircuit.capacity V input.length) :=
  CellsTokensAlignment.cells_eq_streams V input (VerifierCircuit.capacity V input.length)
    (capacity_within V input)

theorem trace (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (ha : Agrees V slots labels exit program) (base : K → List Bool) (input : List Bool)
    (ready : Ready V slots base input) (ambient : σ) :
    (advance (TM2.step program))^[steps V input]
      (some ⟨some (labels .control), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots .reversed) (slots .count) base
        (InitializationTemplate.initializationTokens V input)⟩ := by
  let first := InitializationControl.tokens V
  let middle := InitializationControl.cells V input (VerifierCircuit.capacity V input.length)
  let b₁ := emitted (slots .reversed) (slots .count) base first
  let b₂ := emitted (slots .reversed) (slots .count) b₁ middle
  have h₁ := InitializationControl.trace V (placedControl slots) (labels .control)
    (some (labels (.cells (.prefix .capacityFirst)))) program (ha .control) base (clean ambient)
  change (advance (TM2.step program))^[1]
    (some ⟨some (labels .control), clean ambient, base⟩) =
    some ⟨some (labels (.cells (.prefix .capacityFirst))), clean ambient, b₁⟩ at h₁
  have h₂ := CellsMachine.trace (cellsSlots.trans slots) (cellsLabels labels)
    (some (labels (.validity (.nonempty .initialize))))
    (InputCellsMachine.prefixTruth V) (PayloadCellsMachine.symbolTable V)
    (PaddingCellsMachine.blankRow V) program (fun l => ha (.cells l)) b₁
    (WitnessEncoding.inputPrefix input) (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length) (capacity_within V input)
    (ready.afterEmitted first).cellsReady ambient
  rw [cellsTokens_eq] at h₂
  change (advance (TM2.step program))^[CellsMachine.steps (PayloadCellsMachine.symbolTable V)
    (WitnessEncoding.inputPrefix input).length (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length)]
    (some ⟨some (labels (.cells (.prefix .capacityFirst))), clean ambient, b₁⟩) =
    some ⟨some (labels (.validity (.nonempty .initialize))), clean ambient, b₂⟩ at h₂
  have h₃ := ValidityMachine.Full.trace ((validitySlots 9).trans slots)
    (fun l => labels (.validity l)) exit program (fun l => ha (.validity l)) b₂
    (V.witnessBound.eval input.length)
    ((ready.afterEmitted first).afterEmitted middle).validityReady ambient
  have h := ClashMachine.chain (ClashMachine.chain h₁ h₂) h₃
  simpa only [steps, b₂, b₁, first, middle,
    show ((validitySlots 9).trans slots) 7 = slots .reversed from rfl,
    show ((validitySlots 9).trans slots) 8 = slots .count from rfl,
    ClashMachine.emitted_append (slots .reversed) (slots .count)
      (slots.injective.ne (by decide : (Tape.reversed : Tape 9) ≠ .count)),
    InitializationControl.initializationTokens_eq_blocks] using h

def program (V : NPVerifier) :
    Label V → TM2.Stmt (fun _ : Tape 9 => Bool) (Label V) (State Unit) :=
  statement V (Function.Embedding.refl _) (Function.Embedding.refl _) none

def machine (V : NPVerifier) : FinTM2 where
  K := Tape 9
  k₀ := .rawInput
  k₁ := .reversed
  Γ := fun _ => Bool
  Λ := Label V
  main := .control
  σ := State Unit
  initialState := clean ()
  Γk₀Fin := inferInstance
  m := program V

theorem machineTrace (V : NPVerifier) (base : Tape 9 → List Bool) (input : List Bool)
    (ready : Ready V (Function.Embedding.refl _) base input) :
    (advance (machine V).step)^[steps V input]
      (some ⟨some .control, clean (), base⟩) =
      some ⟨none, clean (), emitted .reversed .count base
        (InitializationTemplate.initializationTokens V input)⟩ :=
  trace V (Function.Embedding.refl _) (Function.Embedding.refl _) none
    (program V) (fun _ => rfl) base input ready ()

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  InitializationAssemblyBounds.timePolynomial V

theorem steps_le_timePolynomial (V : NPVerifier) (input : List Bool) :
    steps V input ≤ (timePolynomial V).eval input.length :=
  InitializationAssemblyBounds.steps_le V input

def inPolynomialTime (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (ha : Agrees V slots labels exit program) (base : K → List Bool) (input : List Bool)
    (ready : Ready V slots base input) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .control), clean ambient, base⟩
      (some ⟨exit, clean ambient, emitted (slots .reversed) (slots .count) base
        (InitializationTemplate.initializationTokens V input)⟩)
      ((timePolynomial V).eval input.length) where
  steps := steps V input
  evals_in_steps := by
    change (advance (TM2.step program))^[steps V input] _ = _
    exact trace V slots labels exit program ha base input ready ambient
  steps_le_m := steps_le_timePolynomial V input

def machineInPolynomialTime (V : NPVerifier) (base : Tape 9 → List Bool) (input : List Bool)
    (ready : Ready V (Function.Embedding.refl _) base input) :
    StateTransition.EvalsToInTime (machine V).step
      ⟨some .control, clean (), base⟩
      (some ⟨none, clean (), emitted .reversed .count base
        (InitializationTemplate.initializationTokens V input)⟩)
      ((timePolynomial V).eval input.length) :=
  inPolynomialTime V (Function.Embedding.refl _) (Function.Embedding.refl _) none
    (program V) (fun _ => rfl) base input ready ()

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

open Turing

inductive Work
  | transition (tape : TransitionArena.Tape)
  | validity (index : Fin 7)
  | cells (index : Fin 9)
  | finish (tape : CircuitFinish.Tape)
  | bootstrap
  deriving DecidableEq, Fintype

abbrev Tape (V : NPVerifier) := VerifierFront.Tape V ⊕ Work
abbrev Alphabet (V : NPVerifier) (_ : Tape V) := Bool
abbrev State := TermMachine.State
abbrev initialState : State := TermMachine.initialState

def frontPorts (V : NPVerifier) : VerifierFront.Tape V ↪ Tape V :=
  ⟨Sum.inl, Sum.inl_injective⟩

def raw (V : NPVerifier) : Tape V := .inl (VerifierFront.raw V)
def framed (V : NPVerifier) : Tape V := .inl (VerifierFront.stream V)
def clock (V : NPVerifier) (c : ClockPreparation.Clock) : Tape V :=
  .inl (VerifierFront.clockTape V c)
def q (V : NPVerifier) : Tape V := clock V .witness
def capacity (V : NPVerifier) : Tape V := clock V .capacity
def countdown (V : NPVerifier) : Tape V := clock V .horizon
def freeInputs (V : NPVerifier) : Tape V := clock V .inputCount

def shared (V : NPVerifier) (t : ForestStage.Tape) : Tape V :=
  .inr (.transition (.inl t))
def current (V : NPVerifier) : Tape V := shared V (.lower .current)
def roots (V : NPVerifier) : Tape V := shared V .rootTable
def records (V : NPVerifier) : Tape V := shared V .records
def tokens (V : NPVerifier) : Tape V := shared V .tokens
def count (V : NPVerifier) : Tape V := shared V (.lower .remaining)
def cursor (V : NPVerifier) : Tape V := .inr (.transition (.inr .cursor))
def output (V : NPVerifier) : Tape V := .inr (.finish .output)

theorem clock_injective (V : NPVerifier) : Function.Injective (clock V) := by
  intro a b h
  have hs := (VerifierFront.clockSlots V).injective (Sum.inl.inj h)
  have ho := ClockPreparation.outputSlot_injective _ hs
  cases a <;> cases b <;> simp_all [ClockPreparation.clockOutput] <;> cases ho

@[simp] theorem clock_eq_iff (V : NPVerifier) (a b : ClockPreparation.Clock) :
    clock V a = clock V b ↔ a = b := (clock_injective V).eq_iff

@[simp] theorem clock_ne_raw (V : NPVerifier) (c : ClockPreparation.Clock) :
    clock V c ≠ raw V := by
  simp [clock, raw, VerifierFront.clockTape, VerifierFront.clockSlots, VerifierFront.raw]

@[simp] theorem raw_ne_clock (V : NPVerifier) (c : ClockPreparation.Clock) :
    raw V ≠ clock V c := (clock_ne_raw V c).symm

@[simp] theorem clock_ne_framed (V : NPVerifier) (c : ClockPreparation.Clock) :
    clock V c ≠ framed V := by
  simp [clock, framed, VerifierFront.clockTape, VerifierFront.clockSlots, VerifierFront.stream]

@[simp] theorem framed_ne_clock (V : NPVerifier) (c : ClockPreparation.Clock) :
    framed V ≠ clock V c := (clock_ne_framed V c).symm

@[simp] theorem raw_ne_framed (V : NPVerifier) : raw V ≠ framed V := by
  simp [raw, framed, VerifierFront.raw, VerifierFront.stream]

def transitionTape (V : NPVerifier) : TransitionArena.Tape → Tape V
  | .inr .raw => raw V
  | .inr .q => q V
  | .inr .capacity => capacity V
  | .inr .countdown => countdown V
  | t => .inr (.transition t)

def transitionPorts (V : NPVerifier) : TransitionArena.Tape ↪ Tape V where
  toFun := transitionTape V
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => simpa [transitionTape] using h
      | inr b =>
        cases b <;>
          simp_all [transitionTape, raw, q, capacity, countdown, clock]
    | inr a =>
      cases b with
      | inl b =>
        cases a <;>
          simp_all [transitionTape, raw, q, capacity, countdown, clock]
      | inr b =>
        cases a <;> cases b <;>
          simp_all [transitionTape, q, capacity, countdown, raw, clock,
            VerifierFront.raw, VerifierFront.clockTape, VerifierFront.clockSlots,
            ClockPreparation.clockOutput] <;>
          cases h

@[simp] theorem transitionPorts_apply (V : NPVerifier) (t : TransitionArena.Tape) :
    transitionPorts V t = transitionTape V t := rfl

def forestPorts (V : NPVerifier) : ForestStage.Tape ↪ Tape V :=
  TransitionArena.forestPorts.trans (transitionPorts V)

def termPorts (V : NPVerifier) : TermMachine.Tape ↪ Tape V :=
  TransitionArena.termPorts.trans (transitionPorts V)

def initializationTape (V : NPVerifier) : InitializationAssembly.Tape 9 → Tape V
  | .rawInput => raw V
  | .framedInput => framed V
  | .witnessBound => q V
  | .capacity => capacity V
  | .reversed => tokens V
  | .count => count V
  | .validityWork j => .inr (.validity j)
  | .cellWork j => .inr (.cells j)

def initializationPorts (V : NPVerifier) : InitializationAssembly.Tape 9 ↪ Tape V where
  toFun := initializationTape V
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [initializationTape, q, capacity, tokens, count, shared,
        raw, framed, clock, VerifierFront.raw, VerifierFront.stream,
        VerifierFront.clockTape, VerifierFront.clockSlots,
        ClockPreparation.clockOutput]
    all_goals
      have impossible := (ClockPreparation.outputSlot_injective (ClockPreparation.clockPolynomials V)) h
      cases impossible

@[simp] theorem initializationPorts_apply (V : NPVerifier) (t : InitializationAssembly.Tape 9) :
    initializationPorts V t = initializationTape V t := rfl

def finishTape (V : NPVerifier) : CircuitFinish.Tape → Tape V
  | .current => current V
  | .freeInputs => freeInputs V
  | .root => roots V
  | .reversedRecords => records V
  | .output => output V
  | .gateCount => .inr (.finish .gateCount)
  | .scratch => .inr (.finish .scratch)

def finishPorts (V : NPVerifier) : CircuitFinish.Tape ↪ Tape V where
  toFun := finishTape V
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [finishTape, current, freeInputs, roots, records, output, shared, clock]

@[simp] theorem finishPorts_apply (V : NPVerifier) (t : CircuitFinish.Tape) :
    finishPorts V t = finishTape V t := rfl

def bootstrapPorts (V : NPVerifier) : ProducerBootstrap.Ports (Tape V) where
  toFun := ![freeInputs V, current V, .inr .bootstrap, count V, cursor V]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp_all [freeInputs, current, count, cursor, shared, clock]

@[simp] theorem bootstrap_source (V : NPVerifier) : bootstrapPorts V 0 = freeInputs V := rfl
@[simp] theorem bootstrap_current (V : NPVerifier) : bootstrapPorts V 1 = current V := rfl
@[simp] theorem bootstrap_scratch (V : NPVerifier) :
    bootstrapPorts V 2 = .inr .bootstrap := rfl
@[simp] theorem bootstrap_count (V : NPVerifier) : bootstrapPorts V 3 = count V := rfl
@[simp] theorem bootstrap_cursor (V : NPVerifier) : bootstrapPorts V 4 = cursor V := rfl

def empty (V : NPVerifier) : Tape V → List Bool := fun _ => []

def frontTapes (V : NPVerifier) (contents : VerifierFront.Tape V → List Bool) :
    Tape V → List Bool
  | .inl t => contents t
  | .inr _ => []

@[simp] theorem frontTapes_at (V : NPVerifier)
    (contents : VerifierFront.Tape V → List Bool) (t : VerifierFront.Tape V) :
    frontTapes V contents (frontPorts V t) = contents t := rfl

@[simp] theorem frontTapes_work (V : NPVerifier)
    (contents : VerifierFront.Tape V → List Bool) (t : Work) :
    frontTapes V contents (.inr t) = [] := rfl

theorem front_fill (V : NPVerifier) (contents : VerifierFront.Tape V → List Bool) :
    ForestPlacement.fill (frontPorts V) (empty V) contents = frontTapes V contents := by
  funext t
  cases t with
  | inl t => exact ForestPlacement.fill_at (frontPorts V) (empty V) contents t
  | inr t =>
    exact ForestPlacement.fill_other (frontPorts V) (empty V) contents _
      (by intro i; simp [frontPorts])

def initialTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  frontTapes V (VerifierFront.frameTapes V input)

theorem initialTapes_eq (V : NPVerifier) (input : List Bool) :
    initialTapes V input = fun t => if t = raw V then input else [] := by
  funext t
  cases t with
  | inl t =>
    cases t with
    | inl i => fin_cases i <;> simp [initialTapes, frontTapes, VerifierFront.frameTapes,
        raw, VerifierFront.raw]
    | inr t => simp [initialTapes, frontTapes, VerifierFront.frameTapes, raw, VerifierFront.raw]
  | inr t => simp [initialTapes, frontTapes, raw]

def frontendPrepared (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  frontTapes V (VerifierFront.preparedTapes V input)

@[simp] theorem frontendPrepared_raw (V : NPVerifier) (input : List Bool) :
    frontendPrepared V input (raw V) = input := VerifierFront.prepared_raw V input

@[simp] theorem frontendPrepared_framed (V : NPVerifier) (input : List Bool) :
    frontendPrepared V input (framed V) = encodeWord input.length ++ input :=
  VerifierFront.prepared_stream V input

@[simp] theorem frontendPrepared_clock (V : NPVerifier) (input : List Bool)
    (c : ClockPreparation.Clock) : frontendPrepared V input (clock V c) =
      encodeWord (ClockPreparation.clockValue V input.length c) :=
  VerifierFront.prepared_clock V input c

@[simp] theorem frontendPrepared_work (V : NPVerifier) (input : List Bool) (t : Work) :
    frontendPrepared V input (.inr t) = [] := rfl

theorem bootstrapReady (V : NPVerifier) (input : List Bool) :
    ProducerBootstrap.Ready (bootstrapPorts V) (frontendPrepared V input)
      (2 * V.witnessBound.eval input.length + 1) := by
  exact ⟨frontendPrepared_clock V input .inputCount, rfl, rfl, rfl, rfl⟩

def bootstrapPrepared (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  ProducerBootstrap.prepared (bootstrapPorts V) (frontendPrepared V input)

@[simp] theorem bootstrapPrepared_front (V : NPVerifier) (input : List Bool)
    (t : VerifierFront.Tape V) :
    bootstrapPrepared V input (frontPorts V t) = VerifierFront.preparedTapes V input t := by
  apply ProducerBootstrap.prepared_other
  all_goals simp [frontPorts, bootstrapPorts, current, count, cursor, shared]

@[simp] theorem bootstrapPrepared_current (V : NPVerifier) (input : List Bool) :
    bootstrapPrepared V input (current V) =
      encodeWord (2 * V.witnessBound.eval input.length + 1) :=
  ProducerBootstrap.prepared_current (bootstrapPorts V) (frontendPrepared V input) _
    (bootstrapReady V input)

@[simp] theorem bootstrapPrepared_count (V : NPVerifier) (input : List Bool) :
    bootstrapPrepared V input (count V) = encodeWord 0 :=
  ProducerBootstrap.prepared_count (bootstrapPorts V) (frontendPrepared V input) _
    (bootstrapReady V input)

@[simp] theorem bootstrapPrepared_cursor (V : NPVerifier) (input : List Bool) :
    bootstrapPrepared V input (cursor V) = encodeWord 0 :=
  ProducerBootstrap.prepared_cursor (bootstrapPorts V) (frontendPrepared V input) _
    (bootstrapReady V input)

theorem bootstrapPrepared_other (V : NPVerifier) (input : List Bool) (t : Tape V)
    (hc : t ≠ current V) (ht : t ≠ count V) (hz : t ≠ cursor V) :
    bootstrapPrepared V input t = frontendPrepared V input t :=
  ProducerBootstrap.prepared_other (bootstrapPorts V) (frontendPrepared V input) t hc ht hz

def initializationBase (V : NPVerifier) (input : List Bool) :
    InitializationAssembly.Tape 9 → List Bool
  | .rawInput => input
  | .framedInput => encodeWord input.length ++ input
  | .witnessBound => encodeWord (V.witnessBound.eval input.length)
  | .capacity => encodeWord (VerifierCircuit.capacity V input.length)
  | .count => encodeWord 0
  | _ => []

theorem bootstrap_initialization_view (V : NPVerifier) (input : List Bool) :
    (fun t => bootstrapPrepared V input (initializationPorts V t)) =
      initializationBase V input := by
  funext t
  cases t <;>
    simp [initializationTape, initializationBase, bootstrapPrepared,
      ProducerBootstrap.prepared, ProducerBootstrap.copied,
      frontendPrepared, frontTapes, current, count, cursor, tokens, shared,
      raw, framed, q, capacity, freeInputs, clock,
      VerifierFront.prepared_raw, VerifierFront.prepared_stream, VerifierFront.prepared_clock,
      ClockPreparation.clockValue, encodeWord]

theorem initializationValidityReady (V : NPVerifier) (input : List Bool) :
    ClashMachine.Full.Ready (InitializationAssembly.validitySlots 9)
      (fun t => bootstrapPrepared V input (initializationPorts V t))
      (V.witnessBound.eval input.length) := by
  rw [bootstrap_initialization_view]
  exact InitializationAssembly.validityReady _ _ rfl (fun _ => rfl)

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerFrontStage

open Turing ProducerArena

abbrev Label (V : NPVerifier) := VerifierFront.Label V ⊕ ProducerBootstrap.Label

def entry (V : NPVerifier) : Label V := .inl (.inl 0)

def statement {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ) :
    Label V → TM2.Stmt (Alphabet V) Λ State
  | .inl l => ForestPlacement.statement (frontPorts V) (fun l => labels (.inl l))
      (some (labels (.inr .copy))) (VerifierFront.program (A := Unit × Bool) V l)
  | .inr l => ProducerBootstrap.statement (bootstrapPorts V) (fun l => labels (.inr l)) exit l

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  VerifierFront.timePolynomial V +
    Polynomial.C 2 * WitnessEncoding.freeInputPolynomial V.witnessBound + Polynomial.C 5

theorem timePolynomial_eval (V : NPVerifier) (n : Nat) :
    (timePolynomial V).eval n = (VerifierFront.timePolynomial V).eval n +
      (2 * (2 * V.witnessBound.eval n + 1) + 5) := by
  simp [timePolynomial, Nat.add_assoc]

def inTime {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet V) Λ State)
    (code : ∀ l, program (labels l) = statement V labels exit l)
    (input : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), initialState, initialTapes V input⟩
      (some ⟨exit, initialState, bootstrapPrepared V input⟩)
      ((timePolynomial V).eval input.length) := by
  have front := ForestPlacement.execution (frontPorts V)
    (fun l => labels (.inl l)) (some (labels (.inr .copy))) (empty V)
    (VerifierFront.program (A := Unit × Bool) V) program (fun l => code (.inl l))
    (VerifierFront.prepareInTime V input ((), false))
  have front' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), initialState, initialTapes V input⟩
      (some ⟨some (labels (.inr .copy)), initialState, frontendPrepared V input⟩)
      ((VerifierFront.timePolynomial V).eval input.length) := by
    simpa only [ForestPlacement.configuration, ForestPlacement.placedLabel,
      front_fill, entry, initialTapes, frontendPrepared, initialState,
      TermMachine.initialState] using front
  have boot := ProducerBootstrap.inTime (bootstrapPorts V) (fun l => labels (.inr l))
    exit program (fun l => code (.inr l)) (frontendPrepared V input)
    (2 * V.witnessBound.eval input.length + 1) (bootstrapReady V input) ((), false) none
  have combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ front' boot
  simpa only [timePolynomial_eval, bootstrapPrepared, initialState,
    TermMachine.initialState, Nat.add_comm] using combined

def program (V : NPVerifier) : Label V → TM2.Stmt (Alphabet V) (Label V) State :=
  statement V id none

def programInTime (V : NPVerifier) (input : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (entry V), initialState, initialTapes V input⟩
      (some ⟨none, initialState, bootstrapPrepared V input⟩)
      ((timePolynomial V).eval input.length) :=
  inTime V id none (program V) (fun _ => rfl) input

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerFrontStage

end

end OAI
