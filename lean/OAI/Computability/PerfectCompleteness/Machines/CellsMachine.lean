import OAI.Computability.PerfectCompleteness.Machines.InputCellsMachineLemmas
import OAI.Computability.PerfectCompleteness.Machines.PaddingCellsMachine
import OAI.Computability.PerfectCompleteness.Machines.PayloadRowsLoop

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.CellsMachine

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
  have rowPort (j : Fin 9) :
      PayloadRowsLoop.rowPorts (loopPorts p) j = p (![1, 8, 9, 10, 11, 7, 12, 3, 4] j) := by
    fin_cases j <;> rfl
  constructor
  · simpa [rowPort, p.injective.eq_iff] using hq
  · change Function.update base (p 8) (encodeWord 0) (p 8) = encodeWord 0
    simp
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
    have capacityPort (j : Fin 4) :
        CellsPrefixStage.capacityPorts (prefixPorts p) j = p (![5, 3, 4, 6] j) := by
      unfold prefixPorts
      rw [prefixMap.eq_1]
      fin_cases j <;> rfl
    have corePort (j : Fin 3) :
        InputCellsCapacity.corePorts (CellsPrefixStage.capacityPorts (prefixPorts p)) j =
          p (![5, 3, 4] j) := by
      fin_cases j <;> rfl
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [InputCellsCapacity.tapes, InputCellsMachine.tapes,
        corePort, capacityPort, emitted, p.injective.eq_iff, ready.empty 5 (by decide)]
      change Function.update (_ : K → List Bool) (p 4)
        (List.replicate (A * input.length) true ++ base (p 4)) (p 4) =
          List.replicate (A * input.length) true ++ base (p 4)
      simp
    · intro k hk
      simp [InputCellsCapacity.tapes, InputCellsMachine.tapes,
        corePort, capacityPort, emitted, hk]
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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.CellsMachine

end OAI
