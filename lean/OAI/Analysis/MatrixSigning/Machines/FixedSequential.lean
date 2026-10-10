import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedStackMachine

namespace OAI

section

namespace KS.W29.FixedSequential

structure Program (k : Nat) where
  states : Nat
  initial : Fin states
  input : Fin k
  output : Fin k
  table : List (KS.W01.FixedStack.Instruction k states)

def Program.toMachine {k : Nat} (P : Program k) : KS.W01.FixedStack.Machine :=
  ⟨k, P.states, P.initial, P.input, P.output, P.table⟩

def ofMachine (M : KS.W01.FixedStack.Machine) : Program M.stackCount :=
  ⟨M.states, M.initial, M.inputStack, M.outputStack, M.table⟩

@[simp] theorem toMachine_ofMachine (M : KS.W01.FixedStack.Machine) : (ofMachine M).toMachine = M := by
  cases M
  rfl

@[simp] theorem ofMachine_toMachine {k : Nat} (P : Program k) : ofMachine P.toMachine = P := by
  cases P
  rfl

def leftState {k : Nat} (P Q : Program k) (s : Fin P.states) : Fin (P.states + Q.states) :=
  ⟨s.val, by have h := s.isLt; omega⟩

def rightState {k : Nat} (P Q : Program k) (s : Fin Q.states) : Fin (P.states + Q.states) :=
  ⟨P.states + s.val, by have h := s.isLt; omega⟩

def liftLeft {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states) :
    KS.W01.FixedStack.Config k (P.states + Q.states) :=
  ⟨some (match c.state with
      | none => rightState P Q Q.initial
      | some s => leftState P Q s), c.«stacks»⟩

def liftRight {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k Q.states) :
    KS.W01.FixedStack.Config k (P.states + Q.states) :=
  ⟨c.state.map (rightState P Q), c.«stacks»⟩

def leftInstruction {k : Nat} (P Q : Program k) (i : KS.W01.FixedStack.Instruction k P.states) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states) :=
  ⟨some (match i.next with
      | none => rightState P Q Q.initial
      | some s => leftState P Q s), i.actions⟩

def rightInstruction {k : Nat} (P Q : Program k) (i : KS.W01.FixedStack.Instruction k Q.states) :
    KS.W01.FixedStack.Instruction k (P.states + Q.states) :=
  ⟨i.next.map (rightState P Q), i.actions⟩

def fetch {k : Nat} (P : Program k) (s : Fin P.states) (heads : Fin k → Fin 3) (b : Bool) :
    KS.W01.FixedStack.Instruction k P.states :=
  P.table.getD (KS.W01.FixedStack.tableIndex s heads b).val (KS.W01.FixedStack.Instruction.halt k P.states)

def dispatch {k : Nat} (P Q : Program k) (s : Fin (P.states + Q.states))
    (heads : Fin k → Fin 3) (b : Bool) : KS.W01.FixedStack.Instruction k (P.states + Q.states) :=
  if h : s.val < P.states then
    leftInstruction P Q (fetch P ⟨s.val, h⟩ heads b)
  else
    rightInstruction P Q
      (fetch Q ⟨s.val - P.states, by have hs := s.isLt; omega⟩ heads b)

def compose {k : Nat} (P Q : Program k) : Program k :=
  ofMachine (KS.W01.FixedStack.compile (leftState P Q P.initial) P.input Q.output (dispatch P Q))

@[simp] theorem compose_toMachine {k : Nat} (P Q : Program k) :
    (compose P Q).toMachine =
      KS.W01.FixedStack.compile (leftState P Q P.initial) P.input Q.output (dispatch P Q) :=
  toMachine_ofMachine _

@[simp] theorem compose_input {k : Nat} (P Q : Program k) : (compose P Q).input = P.input := rfl
@[simp] theorem compose_output {k : Nat} (P Q : Program k) : (compose P Q).output = Q.output := rfl

theorem dispatch_left {k : Nat} (P Q : Program k) (s : Fin P.states)
    (heads : Fin k → Fin 3) (b : Bool) :
    dispatch P Q (leftState P Q s) heads b = leftInstruction P Q (fetch P s heads b) := by
  simp [dispatch, leftState, s.isLt]

theorem dispatch_right {k : Nat} (P Q : Program k) (s : Fin Q.states)
    (heads : Fin k → Fin 3) (b : Bool) :
    dispatch P Q (rightState P Q s) heads b = rightInstruction P Q (fetch Q s heads b) := by
  simp [dispatch, rightState]

theorem step_left {k : Nat} (P Q : Program k) (s : Fin P.states)
    («stacks» : Fin k → List Bool) (b : Bool) :
    (compose P Q).toMachine.step ⟨some (leftState P Q s), «stacks»⟩ b =
      liftLeft P Q (P.toMachine.step ⟨some s, «stacks»⟩ b) := by
  change (KS.W01.FixedStack.compile (leftState P Q P.initial) P.input Q.output
    (dispatch P Q)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_left]
  rfl

theorem step_right {k : Nat} (P Q : Program k) (s : Fin Q.states)
    («stacks» : Fin k → List Bool) (b : Bool) :
    (compose P Q).toMachine.step ⟨some (rightState P Q s), «stacks»⟩ b =
      liftRight P Q (Q.toMachine.step ⟨some s, «stacks»⟩ b) := by
  change (KS.W01.FixedStack.compile (leftState P Q P.initial) P.input Q.output
    (dispatch P Q)).step _ _ = _
  erw [KS.W01.FixedStack.step_compile]
  dsimp only
  rw [dispatch_right]
  rfl

theorem step_liftRight {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k Q.states) (b : Bool) :
    (compose P Q).toMachine.step (liftRight P Q c) b =
      liftRight P Q (Q.toMachine.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s => exact step_right P Q s «stacks» b

theorem run_liftRight {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k Q.states) (bits : List Bool) :
    (compose P Q).toMachine.run (liftRight P Q c) bits =
      liftRight P Q (Q.toMachine.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (compose P Q).toMachine.run
        ((compose P Q).toMachine.step (liftRight P Q c) b) bs =
        liftRight P Q (Q.toMachine.run (Q.toMachine.step c b) bs)
      erw [step_liftRight P Q c b]
      exact ih (Q.toMachine.step c b)

def ActiveFor {k : Nat} (P : Program k) : KS.W01.FixedStack.Config k P.states → List Bool → Prop
  | _, [] => True
  | c, b :: bs => c.state ≠ none ∧ ActiveFor P (P.toMachine.step c b) bs

theorem activeFor_append {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (first rest : List Bool) :
    ActiveFor P c (first ++ rest) ↔
      ActiveFor P c first ∧ ActiveFor P (P.toMachine.run c first) rest := by
  induction first generalizing c with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons b bs ih =>
      simp only [List.cons_append, ActiveFor, KS.W01.FixedStack.Machine.run, ih (P.toMachine.step c b), and_assoc]

def HaltsAfter {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool) : Prop :=
  ActiveFor P c bits ∧ (P.toMachine.run c bits).state = none

theorem step_liftLeft {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states) (b : Bool)
    (h : c.state ≠ none) :
    (compose P Q).toMachine.step (liftLeft P Q c) b =
      liftLeft P Q (P.toMachine.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => exact (h rfl).elim
  | some s => exact step_left P Q s «stacks» b

theorem run_liftLeft {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool)
    (h : ActiveFor P c bits) :
    (compose P Q).toMachine.run (liftLeft P Q c) bits = liftLeft P Q (P.toMachine.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (compose P Q).toMachine.run
        ((compose P Q).toMachine.step (liftLeft P Q c) b) bs =
        liftLeft P Q (P.toMachine.run (P.toMachine.step c b) bs)
      erw [step_liftLeft P Q c b h.1]
      exact ih _ h.2

theorem run_compose {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (first second : List Bool) (h : HaltsAfter P c first) :
    (compose P Q).toMachine.run (liftLeft P Q c) (first ++ second) =
      liftRight P Q (Q.toMachine.run ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ second) := by
  erw [KS.W01.FixedStack.Machine.run_append, run_liftLeft P Q c first h.1]
  have he : liftLeft P Q (P.toMachine.run c first) =
      liftRight P Q ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ := by
    simp [liftLeft, liftRight, h.2]
  rw [he, run_liftRight]
  rfl

theorem activeFor_liftLeft {k : Nat} (P Q : Program k)
    (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool) (h : ActiveFor P c bits) :
    ActiveFor (compose P Q) (liftLeft P Q c) bits := by
  induction bits generalizing c with
  | nil => trivial
  | cons b bs ih =>
      refine ⟨Option.some_ne_none _, ?_⟩
      rw [step_liftLeft P Q c b h.1]
      exact ih _ h.2

theorem activeFor_liftRight {k : Nat} (P Q : Program k)
    (c : KS.W01.FixedStack.Config k Q.states) (bits : List Bool) (h : ActiveFor Q c bits) :
    ActiveFor (compose P Q) (liftRight P Q c) bits := by
  induction bits generalizing c with
  | nil => trivial
  | cons b bs ih =>
      refine ⟨?_, ?_⟩
      · have hc := h.1
        cases hs : c.state with
        | none => exact (hc hs).elim
        | some state =>
            change c.state.map (rightState P Q) ≠ none
            rw [hs]
            exact Option.some_ne_none _
      · rw [step_liftRight]
        exact ih _ h.2

theorem compose_haltsAfter {k : Nat} (P Q : Program k)
    (c : KS.W01.FixedStack.Config k P.states) (first second : List Bool)
    (hfirst : HaltsAfter P c first)
    (hsecond : HaltsAfter Q ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ second) :
    HaltsAfter (compose P Q) (liftLeft P Q c) (first ++ second) := by
  constructor
  · apply (activeFor_append _ _ _ _).2
    refine ⟨activeFor_liftLeft P Q c first hfirst.1, ?_⟩
    rw [run_liftLeft P Q c first hfirst.1]
    have he : liftLeft P Q (P.toMachine.run c first) =
        liftRight P Q ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ := by
      simp [liftLeft, liftRight, hfirst.2]
    rw [he]
    exact activeFor_liftRight P Q _ second hsecond.1
  · rw [run_compose P Q c first second hfirst]
    change (Q.toMachine.run ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ second).state.map
      (rightState P Q) = none
    exact congrArg (Option.map (rightState P Q)) hsecond.2

def HaltsFromWithin {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (fuel : Nat) : Prop :=
  ∀ bits : List Bool, bits.length = fuel → (P.toMachine.run c bits).state = none

theorem exists_halting_prefix {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (bits : List Bool) (h : (P.toMachine.run c bits).state = none) :
    ∃ first rest, bits = first ++ rest ∧ HaltsAfter P c first := by
  induction bits generalizing c with
  | nil => exact ⟨[], [], rfl, ⟨trivial, h⟩⟩
  | cons b bs ih =>
      by_cases hc : c.state = none
      · exact ⟨[], b :: bs, rfl, ⟨trivial, hc⟩⟩
      · obtain ⟨first, rest, heq, ha⟩ := ih (P.toMachine.step c b) h
        refine ⟨b :: first, rest, ?_, ?_⟩
        · simp [heq]
        · exact ⟨⟨hc, ha.1⟩, ha.2⟩

theorem run_compose_within {k : Nat} (P Q : Program k)
    (c : KS.W01.FixedStack.Config k P.states) (fuel : Nat)
    (h : HaltsFromWithin P c fuel) (bits : List Bool) (hlen : fuel ≤ bits.length) :
    ∃ first rest : List Bool, bits = first ++ rest ∧ first.length ≤ fuel ∧
      HaltsAfter P c first ∧
      (compose P Q).toMachine.run (liftLeft P Q c) bits =
        liftRight P Q (Q.toMachine.run
          ⟨some Q.initial, (P.toMachine.run c (bits.take fuel)).«stacks»⟩ rest) := by
  have ht : (bits.take fuel).length = fuel := by
    simp [List.length_take, Nat.min_eq_left hlen]
  obtain ⟨first, leftover, heq, hf⟩ :=
    exists_halting_prefix P c (bits.take fuel) (h _ ht)
  have hfl : first.length ≤ fuel := by
    have hh := congrArg List.length heq
    simp only [List.length_append, ht] at hh
    omega
  have hwhole : bits = first ++ (leftover ++ bits.drop fuel) := by
    calc
      bits = bits.take fuel ++ bits.drop fuel := (List.take_append_drop fuel bits).symm
      _ = first ++ (leftover ++ bits.drop fuel) := by rw [heq, List.append_assoc]
  have hout : P.toMachine.run c (bits.take fuel) = P.toMachine.run c first := by
    erw [heq, KS.W01.FixedStack.Machine.run_append]
    exact P.toMachine.run_halted _ hf.2 leftover
  refine ⟨first, leftover ++ bits.drop fuel, hwhole, hfl, hf, ?_⟩
  rw [hout]
  conv_lhs => rw [hwhole]
  exact run_compose P Q c first _ hf

theorem haltsFromWithin_mono {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states)
    {small large : Nat} (h : HaltsFromWithin P c small) (hle : small ≤ large) :
    HaltsFromWithin P c large := by
  intro bits hbits
  have htake : (bits.take small).length = small := by
    simp [List.length_take, hbits, Nat.min_eq_left hle]
  have hh := h (bits.take small) htake
  conv_lhs => rw [← List.take_append_drop small bits]
  erw [KS.W01.FixedStack.Machine.run_append,
    KS.W01.FixedStack.Machine.run_halted P.toMachine _ hh]
  exact hh

theorem compose_haltsFromWithin {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (t₁ t₂ : Nat) (hfirst : HaltsFromWithin P c t₁)
    (hsecond : ∀ first : List Bool, first.length ≤ t₁ → HaltsAfter P c first →
      HaltsFromWithin Q ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ t₂) :
    HaltsFromWithin (compose P Q) (liftLeft P Q c) (t₁ + t₂) := by
  intro bits hbits
  have hlen : (bits.take t₁).length = t₁ := by simp [List.length_take, hbits]
  obtain ⟨first, leftover, heq, hf⟩ :=
    exists_halting_prefix P c (bits.take t₁) (hfirst _ hlen)
  have hfl : first.length ≤ t₁ := by
    have hh := congrArg List.length heq
    simp only [List.length_append, hlen] at hh
    omega
  have hwhole : bits = first ++ (leftover ++ bits.drop t₁) := by
    calc
      bits = bits.take t₁ ++ bits.drop t₁ := (List.take_append_drop t₁ bits).symm
      _ = first ++ (leftover ++ bits.drop t₁) := by rw [heq, List.append_assoc]
  have hremain : t₂ ≤ (leftover ++ bits.drop t₁).length := by
    have hh := congrArg List.length hwhole
    simp only [List.length_append] at hh ⊢
    omega
  have hn := haltsFromWithin_mono Q _ (hsecond first hfl hf) hremain
  rw [hwhole, run_compose P Q c first _ hf]
  change Option.map (rightState P Q) (Q.toMachine.run
    ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩
    (leftover ++ bits.drop t₁)).state = none
  exact congrArg (Option.map (rightState P Q)) (hn _ rfl)

theorem polynomialFuel_add_le (C₁ C₂ k₁ k₂ n : Nat) :
    KS.W29.polynomialFuel C₁ k₁ n + KS.W29.polynomialFuel C₂ k₂ n ≤
      KS.W29.polynomialFuel (C₁ + C₂) (max k₁ k₂) n := by
  have h₁ := Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_max_left k₁ k₂)
  have h₂ := Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_max_right k₁ k₂)
  unfold KS.W29.polynomialFuel
  calc
    _ ≤ C₁ * (n + 1) ^ max k₁ k₂ + C₂ * (n + 1) ^ max k₁ k₂ :=
      Nat.add_le_add (Nat.mul_le_mul_left C₁ h₁) (Nat.mul_le_mul_left C₂ h₂)
    _ = _ := (Nat.add_mul _ _ _).symm

theorem compose_polynomial {k : Nat} (P Q : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (C₁ C₂ k₁ k₂ n : Nat)
    (hfirst : HaltsFromWithin P c (KS.W29.polynomialFuel C₁ k₁ n))
    (hsecond : ∀ first : List Bool, first.length ≤ KS.W29.polynomialFuel C₁ k₁ n →
      HaltsAfter P c first → HaltsFromWithin Q
        ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ (KS.W29.polynomialFuel C₂ k₂ n)) :
    HaltsFromWithin (compose P Q) (liftLeft P Q c)
      (KS.W29.polynomialFuel (C₁ + C₂) (max k₁ k₂) n) :=
  haltsFromWithin_mono _ _
    (compose_haltsFromWithin P Q c _ _ hfirst hsecond)
    (polynomialFuel_add_le C₁ C₂ k₁ k₂ n)

end KS.W29.FixedSequential

end

end OAI
