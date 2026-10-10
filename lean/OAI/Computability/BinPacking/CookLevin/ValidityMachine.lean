import Mathlib.Tactic.Linarith
import OAI.Computability.BinPacking.CookLevin.ClashMachine

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.OrClosure

open Turing PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

structure Ports (K : Type) where
  remaining : K
  reversed : K
  count : K
  remaining_ne_reversed : remaining ≠ reversed
  remaining_ne_count : remaining ≠ count
  reversed_ne_count : reversed ≠ count

def frame (ports : Ports K) (base : K → List Bool)
    (remaining reversed count : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base ports.remaining remaining)
    ports.reversed reversed) ports.count count

@[simp] theorem frame_remaining (p : Ports K) (base : K → List Bool)
    (remaining reversed count : List Bool) :
    frame p base remaining reversed count p.remaining = remaining := by
  simp [frame, p.remaining_ne_count, p.remaining_ne_reversed]

@[simp] theorem frame_reversed (p : Ports K) (base : K → List Bool)
    (remaining reversed count : List Bool) :
    frame p base remaining reversed count p.reversed = reversed := by
  simp [frame, p.reversed_ne_count]

@[simp] theorem frame_count (p : Ports K) (base : K → List Bool)
    (remaining reversed count : List Bool) :
    frame p base remaining reversed count p.count = count := by
  simp [frame]

theorem frame_other (p : Ports K) (base : K → List Bool)
    (remaining reversed count : List Bool) (k : K)
    (hr : k ≠ p.remaining) (ho : k ≠ p.reversed) (hc : k ≠ p.count) :
    frame p base remaining reversed count k = base k := by
  simp [frame, hr, ho, hc]

@[simp] theorem frame_self (p : Ports K) (base : K → List Bool) :
    frame p base (base p.remaining) (base p.reversed) (base p.count) = base := by
  simp [frame]

@[simp] theorem update_remaining (p : Ports K) (base : K → List Bool)
    (remaining reversed count replacement : List Bool) :
    Function.update (frame p base remaining reversed count) p.remaining replacement =
      frame p base replacement reversed count := by
  funext k
  by_cases hr : k = p.remaining <;> by_cases ho : k = p.reversed <;>
    by_cases hc : k = p.count <;>
    simp_all [frame, p.remaining_ne_reversed, p.remaining_ne_count, p.reversed_ne_count,
      Ne.symm p.remaining_ne_reversed, Ne.symm p.remaining_ne_count, Ne.symm p.reversed_ne_count]

@[simp] theorem update_reversed (p : Ports K) (base : K → List Bool)
    (remaining reversed count replacement : List Bool) :
    Function.update (frame p base remaining reversed count) p.reversed replacement =
      frame p base remaining replacement count := by
  funext k
  by_cases hr : k = p.remaining <;> by_cases ho : k = p.reversed <;>
    by_cases hc : k = p.count <;>
    simp_all [frame, p.remaining_ne_reversed, p.remaining_ne_count, p.reversed_ne_count,
      Ne.symm p.remaining_ne_reversed, Ne.symm p.remaining_ne_count, Ne.symm p.reversed_ne_count]

@[simp] theorem update_count (p : Ports K) (base : K → List Bool)
    (remaining reversed count replacement : List Bool) :
    Function.update (frame p base remaining reversed count) p.count replacement =
      frame p base remaining reversed replacement := by
  simp [frame]

def seed (p : Ports K) (again : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .push p.reversed (fun _ => false)
    (.push p.count (fun _ => true)
      (.load (fun state => (state.1, none)) (.goto fun _ => again)))

def loop (p : Ports K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop p.remaining (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (pushWord p.reversed (encodeWord 4)
        (.push p.count (fun _ => true)
          (.load (fun state => (state.1, none)) (.goto fun _ => again))))
      (.push p.remaining (fun _ => false)
        (.load (fun state => (state.1, none))
          (Reduction.MachineTransfer.exitAt p.remaining exit))))

omit [DecidableEq K] in
theorem seedPushBound (p : Ports K) (again : Λ) :
    Runtime.statementPushBound (seed (σ := σ) p again) = 2 := rfl

omit [DecidableEq K] in
theorem loopPushBound (p : Ports K) (again : Λ) (exit : Option Λ) :
    Runtime.statementPushBound (loop (σ := σ) p again exit) = 6 := by
  cases exit <;> rfl

theorem seedStep (p : Ports K) (again : Λ) (base : K → List Bool)
    (remaining output count : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (seed p again) (ambient, register)
      (frame p base remaining output count) =
      ⟨some again, (ambient, none),
        frame p base remaining (false :: output) (true :: count)⟩ := by
  simp [seed, TM2.stepAux]

theorem loopStep_zero (p : Ports K) (again : Λ) (exit : Option Λ)
    (base : K → List Bool) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop p again exit) (ambient, register)
      (frame p base (encodeWord 0 ++ suffix) output count) =
      ⟨exit, (ambient, none), frame p base (encodeWord 0 ++ suffix) output count⟩ := by
  cases exit <;>
    simp [loop, TM2.stepAux, encodeWord, Reduction.MachineTransfer.exitAt]

theorem loopStep_succ (p : Ports K) (again : Λ) (exit : Option Λ)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop p again exit) (ambient, register)
      (frame p base (encodeWord (n + 1) ++ suffix) output count) =
      ⟨some again, (ambient, none),
        frame p base (encodeWord n ++ suffix)
          ((encodeWord 4).reverse ++ output) (true :: count)⟩ := by
  simp [loop, TM2.stepAux, stepAux_pushWord, encodeWord, List.replicate_succ]

theorem tokenBits_append (first second : List Token) :
    tokenBits (first ++ second) = tokenBits first ++ tokenBits second := by
  simp [tokenBits, tokenWords, encodeWords_append]

@[simp] theorem tokenBits_or : tokenBits [Token.or] = encodeWord 4 := rfl

@[simp] theorem tokenBits_false : tokenBits [Token.const false] = [false] := rfl

theorem tokenBits_closeOr (n : Nat) :
    tokenBits (closeOr n) = [false] ++ tokenBits (List.replicate n Token.or) := by
  unfold closeOr
  rw [tokenBits_append, tokenBits_false]

theorem tokenBits_replicate_succ (n : Nat) :
    tokenBits (List.replicate (n + 1) Token.or) =
      encodeWord 4 ++ tokenBits (List.replicate n Token.or) := by
  rw [List.replicate_succ]
  change tokenBits ([Token.or] ++ List.replicate n Token.or) = _
  rw [tokenBits_append, tokenBits_or]

private theorem replicate_push (n : Nat) (count : List Bool) :
    List.replicate n true ++ true :: count =
      List.replicate (n + 1) true ++ count := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [List.replicate_succ, List.cons_append] using (congrArg (List.cons true) ih)

theorem loopTrace (p : Ports K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program again = loop p again exit)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        frame p base (encodeWord n ++ suffix) output count⟩) =
      some ⟨exit, (ambient, none),
        frame p base (encodeWord 0 ++ suffix)
          ((tokenBits (List.replicate n Token.or)).reverse ++ output)
          (List.replicate n true ++ count)⟩ := by
  induction n generalizing output count register with
  | zero =>
      change some (TM2.stepAux (program again) (ambient, register)
        (frame p base (encodeWord 0 ++ suffix) output count)) = _
      rw [atLoop, loopStep_zero]
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[n + 1]
        (some (TM2.stepAux (program again) (ambient, register)
          (frame p base (encodeWord (n + 1) ++ suffix) output count))) = _
      rw [atLoop, loopStep_succ, ih]
      simp only [tokenBits_replicate_succ, List.reverse_append, List.append_assoc]
      rw [replicate_push]

theorem closureTrace (p : Ports K) (entry again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program entry = seed p again)
    (atLoop : program again = loop p again exit)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some entry, (ambient, register),
        frame p base (encodeWord n ++ suffix) output count⟩) =
      some ⟨exit, (ambient, none),
        frame p base (encodeWord 0 ++ suffix)
          ((tokenBits (closeOr n)).reverse ++ output)
          (List.replicate (n + 1) true ++ count)⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step program))^[n + 1]
    (some (TM2.stepAux (program entry) (ambient, register)
      (frame p base (encodeWord n ++ suffix) output count))) = _
  rw [atSeed, seedStep, loopTrace p again exit program atLoop]
  simp only [tokenBits_closeOr, List.singleton_append, List.reverse_cons, List.append_assoc]
  rw [replicate_push]

def closureInTime (p : Ports K) (entry again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program entry = seed p again)
    (atLoop : program again = loop p again exit)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some entry, (ambient, register), frame p base (encodeWord n ++ suffix) output count⟩
      (some ⟨exit, (ambient, none),
        frame p base (encodeWord 0 ++ suffix)
          ((tokenBits (closeOr n)).reverse ++ output)
          (List.replicate (n + 1) true ++ count)⟩) (n + 2) where
  steps := n + 2
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[n + 2] _ = _
    exact closureTrace p entry again exit program atSeed atLoop
      base n suffix output count ambient register
  steps_le_m := Nat.le_refl _

theorem increment_count (n c : Nat) (suffix : List Bool) :
    List.replicate (n + 1) true ++ (encodeWord c ++ suffix) =
      encodeWord (c + n + 1) ++ suffix := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]
  rw [show n + 1 + c = c + n + 1 by omega]

variable [Fintype K] [Fintype σ]

def machine (p : Ports K) (ambient : σ) : FinTM2 where
  K := K
  k₀ := p.remaining
  k₁ := p.reversed
  Γ := Alphabet
  Λ := Bool
  main := false
  σ := σ × Option Bool
  initialState := (ambient, none)
  Γk₀Fin := inferInstance
  m label := if label then loop p true none else seed p true

theorem machineTrace (p : Ports K) (base : K → List Bool) (n : Nat)
    (suffix output count : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (machine p ambient).step)^[n + 2]
      (some ⟨some false, (ambient, register),
        frame p base (encodeWord n ++ suffix) output count⟩) =
      some ⟨none, (ambient, none),
        frame p base (encodeWord 0 ++ suffix)
          ((tokenBits (closeOr n)).reverse ++ output)
          (List.replicate (n + 1) true ++ count)⟩ := by
  exact closureTrace p false true none (machine p ambient).m rfl rfl
    base n suffix output count ambient register

end BinPackingGames.Foundations.Complexity.CookLevin.OrClosure

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted emitted_append emitted_other emitted_nil)

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

private theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

namespace SelectorLoop

def inputMap : Fin 4 ↪ Fin 5 := ⟨![1, 2, 3, 4], by decide⟩

inductive Label where
  | guard | input (l : ClashMachine.Input.Label) | increment
  deriving DecidableEq, Fintype

def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (done : Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .guard => MachineUnaryCounter.guard (slots 0) (labels (.input .tag)) done
  | .input l => ClashMachine.Input.statement (inputMap.trans slots)
      (fun l => labels (.input l)) (some (labels .increment)) l
  | .increment => .push (slots 1) (fun _ => true) (.goto fun _ => labels .guard)

def frame (slots : Fin 5 ↪ K) (base : K → List Bool) (remaining current : Nat) : K → List Bool :=
  Function.update (Function.update base (slots 0) (encodeWord remaining)) (slots 1) (encodeWord current)

@[simp] theorem frame_current (slots : Fin 5 ↪ K) (base : K → List Bool) (r j : Nat) :
    frame slots base r j (slots 1) = encodeWord j := by simp [frame]

@[simp] theorem frame_remaining (slots : Fin 5 ↪ K) (base : K → List Bool) (r j : Nat) :
    frame slots base r j (slots 0) = encodeWord r := by simp [frame, slots.injective.eq_iff]

theorem counter_frame (slots : Fin 5 ↪ K) (base : K → List Bool) (r r' j : Nat) :
    MachineUnaryCounter.counterTapes (slots 0) (frame slots base r j) r' [] =
      frame slots base r' j := by
  funext k
  by_cases h₀ : k = slots 0
  · subst k; simp [MachineUnaryCounter.counterTapes, frame, slots.injective.eq_iff]
  · by_cases h₁ : k = slots 1 <;> simp [MachineUnaryCounter.counterTapes, frame, h₀, h₁]

theorem emitted_frame (slots : Fin 5 ↪ K) (base : K → List Bool) (r j : Nat) (tokens : List Token) :
    emitted (slots 3) (slots 4) (frame slots base r j) tokens =
      frame slots (emitted (slots 3) (slots 4) base tokens) r j := by
  funext k
  by_cases h₀ : k = slots 0
  · subst k; simp [emitted, frame, slots.injective.eq_iff]
  · by_cases h₁ : k = slots 1
    · subst k; simp [emitted, frame, slots.injective.eq_iff]
    · by_cases h₃ : k = slots 3
      · subst k; simp [emitted, frame, slots.injective.eq_iff]
      · by_cases h₄ : k = slots 4
        · subst k; simp [emitted, frame, slots.injective.eq_iff]
        · simp [emitted, frame, h₀, h₁, h₃, h₄]

theorem increment_frame (slots : Fin 5 ↪ K) (base : K → List Bool) (r j : Nat) :
    Function.update (frame slots base r j) (slots 1) (true :: encodeWord j) =
      frame slots base r (j + 1) := by
  simp [frame, encodeWord, List.replicate_succ]

def tokens (count start : Nat) : List Token :=
  forTokens count (fun j => [.input (start + j)])

theorem tokens_zero (start : Nat) : tokens 0 start = [] := rfl

theorem tokens_succ (count start : Nat) :
    tokens (count + 1) start = [.input start] ++ tokens count (start + 1) := by
  rw [tokens, forTokens_succ_first]
  simp only [Nat.add_zero]
  apply congrArg (List.append [Token.input start])
  apply forTokens_congr
  intro j _
  rw [show start + (j + 1) = start + 1 + j by omega]

def steps : Nat → Nat → Nat
  | 0, _ => 1
  | count + 1, start => 1 + ClashMachine.Input.steps start + 1 + steps count (start + 1)

theorem trace (slots : Fin 5 ↪ K) (labels : Label → Λ) (done : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels done l)
    (base : K → List Bool) (count start : Nat)
    (scratchEmpty : base (slots 2) = []) (ambient : σ) :
    (advance (TM2.step program))^[steps count start]
      (some ⟨some (labels .guard), clean ambient, frame slots base count start⟩) =
      some ⟨some done, clean ambient,
        frame slots (emitted (slots 3) (slots 4) base (tokens count start)) 0 (start + count)⟩ := by
  induction count generalizing base start with
  | zero =>
    have h := MachineUnaryCounter.guardTrace_zero (slots 0) (labels .guard)
      (labels (.input .tag)) done program (atLabels .guard)
      (frame slots base 0 start) [] (ambient, false) none
    simpa only [counter_frame, steps, tokens_zero, emitted_nil, Nat.add_zero, clean] using h
  | succ count ih =>
    have hg := MachineUnaryCounter.guardTrace_succ (slots 0) (labels .guard)
      (labels (.input .tag)) done program (atLabels .guard)
      (frame slots base count start) count [] (ambient, false) none
    simp only [counter_frame] at hg
    have hs : frame slots base count start (slots 2) = [] := by
      simpa [frame, slots.injective.eq_iff] using scratchEmpty
    have hp := ClashMachine.Input.trace (inputMap.trans slots) (fun l => labels (.input l))
      (some (labels .increment)) program (fun _ => atLabels _)
      (frame slots base count start) start (frame_current slots base count start) hs ambient
    change (advance (TM2.step program))^[ClashMachine.Input.steps start]
      (some ⟨some (labels (.input .tag)), clean ambient, frame slots base count start⟩) =
      some ⟨some (labels .increment), clean ambient,
        emitted (slots 3) (slots 4) (frame slots base count start) [.input start]⟩ at hp
    rw [emitted_frame] at hp
    let nextBase := emitted (slots 3) (slots 4) base [.input start]
    have hn : (advance (TM2.step program))^[1]
        (some ⟨some (labels .increment), clean ambient, frame slots nextBase count start⟩) =
        some ⟨some (labels .guard), clean ambient, frame slots nextBase count (start + 1)⟩ := by
      change some (TM2.stepAux (program (labels .increment)) _ _) = _
      rw [atLabels, statement]
      simp only [TM2.stepAux, frame_current, increment_frame]
    have hns : nextBase (slots 2) = [] := by
      simpa [nextBase, emitted, slots.injective.eq_iff] using scratchEmpty
    have hr := ih nextBase (start + 1) hns
    have h := chain (chain (chain hg hp) hn) hr
    rw [show start + 1 + count = start + (count + 1) by omega] at h
    simp only [nextBase, emitted_append (slots 3) (slots 4)
      (slots.injective.ne (by decide : (3 : Fin 5) ≠ 4)), ← tokens_succ] at h
    exact h

theorem steps_le (count start : Nat) :
    steps count start ≤ count * (3 * (start + count + 1) + 5) + 1 := by
  induction count generalizing start with
  | zero => simp [steps]
  | succ count ih =>
    have hr := ih (start + 1)
    have he : start + 1 + count + 1 = start + (count + 1) + 1 := by omega
    rw [he] at hr
    rw [steps, Nat.succ_mul]
    unfold ClashMachine.Input.steps
    omega

end SelectorLoop

namespace Nonempty

def loopMap : Fin 5 ↪ Fin 7 := ⟨![1, 2, 3, 5, 6], by decide⟩

def closurePorts (slots : Fin 7 ↪ K) : OrClosure.Ports K where
  remaining := slots 4
  reversed := slots 5
  count := slots 6
  remaining_ne_reversed := slots.injective.ne (by decide)
  remaining_ne_count := slots.injective.ne (by decide)
  reversed_ne_count := slots.injective.ne (by decide)

inductive Label where
  | initialize
  | remaining (l : MachineUnaryAffineAt.Label)
  | closure (l : MachineUnaryAffineAt.Label)
  | selector (l : SelectorLoop.Label)
  | orSeed | orLoop | cleanup | drain
  deriving DecidableEq, Fintype

def copyStatement (source scratch destination : K)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => MachineUnaryAffineAt.seed destination 1 (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source scratch destination 1 (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false (labels .restore) exit

def statement (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .initialize => .push (slots 2) (fun _ => false) (.goto fun _ => labels (.remaining .seed))
  | .remaining l => copyStatement (slots 0) (slots 3) (slots 1)
      (fun l => labels (.remaining l)) (some (labels (.closure .seed))) l
  | .closure l => copyStatement (slots 0) (slots 3) (slots 4)
      (fun l => labels (.closure l)) (some (labels (.selector .guard))) l
  | .selector l => SelectorLoop.statement (loopMap.trans slots)
      (fun l => labels (.selector l)) (labels .orSeed) l
  | .orSeed => OrClosure.seed (closurePorts slots) (labels .orLoop)
  | .orLoop => OrClosure.loop (closurePorts slots) (labels .orLoop) (some (labels .cleanup))
  | .cleanup => .pop (slots 1) (fun s _ => s)
      (.pop (slots 4) (fun s _ => s) (.goto fun _ => labels .drain))
  | .drain => MachineDrain.drain (slots 2) (labels .drain) exit

def steps (q : Nat) : Nat :=
  1 + (2 * (q + 1) + 1) + (2 * (q + 1) + 1) +
    SelectorLoop.steps (q + 1) 0 + (q + 3) + 1 + (q + 3)

structure Ready (slots : Fin 7 ↪ K) (base : K → List Bool) (q : Nat) : Prop where
  boundWord : base (slots 0) = encodeWord q
  remainingEmpty : base (slots 1) = []
  currentEmpty : base (slots 2) = []
  scratchEmpty : base (slots 3) = []
  closureEmpty : base (slots 4) = []

private theorem emitted_update (output count work : K) (ho : work ≠ output) (hc : work ≠ count)
    (base : K → List Bool) (replacement : List Bool) (tokens : List Token) :
    emitted output count (Function.update base work replacement) tokens =
      Function.update (emitted output count base tokens) work replacement := by
  funext k
  by_cases hw : k = work
  · subst k; simp [emitted, ho, hc]
  · by_cases houtput : k = output
    · subst k
      by_cases hoc : output = count
      · subst count; simp [emitted, Ne.symm ho]
      · simp [emitted, Ne.symm ho, Ne.symm hc, hoc]
    · by_cases hcount : k = count
      · subst k; simp [emitted, Ne.symm hc]
      · simp [emitted, hw, houtput, hcount]

private theorem frame_updates (slots : Fin 7 ↪ K) (base : K → List Bool) (r i : Nat) :
    SelectorLoop.frame (loopMap.trans slots) base r i =
      Function.update (Function.update base (slots 1) (encodeWord r)) (slots 2) (encodeWord i) := rfl

private theorem tokens_nonempty (q : Nat) :
    SelectorLoop.tokens (q + 1) 0 ++ closeOr (q + 1) = nonemptyTokens q := by
  simp [SelectorLoop.tokens, nonemptyTokens]

private theorem closed_frame (p : OrClosure.Ports K) (base : K → List Bool) (n : Nat) :
    OrClosure.frame p base (encodeWord 0)
      ((tokenBits (closeOr n)).reverse ++ base p.reversed)
      (List.replicate (n + 1) true ++ base p.count) =
      emitted p.reversed p.count (Function.update base p.remaining (encodeWord 0)) (closeOr n) := by
  simp only [OrClosure.frame, emitted, closeOr, List.length_append, List.length_singleton,
    List.length_replicate]
  rw [Nat.add_comm 1 n]
  simp only [Function.update_of_ne (Ne.symm p.remaining_ne_reversed),
    Function.update_of_ne (Ne.symm p.remaining_ne_count)]

theorem trace (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[steps q]
      (some ⟨some (labels .initialize), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 5) (slots 6) base (nonemptyTokens q)⟩ := by
  let started := Function.update base (slots 2) (encodeWord 0)
  let remaining := Function.update started (slots 1) (encodeWord (q + 1))
  let prepared := Function.update remaining (slots 4) (encodeWord (q + 1))
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize), clean ambient, base⟩) =
      some ⟨some (labels (.remaining .seed)), clean ambient, started⟩ := by
    change some (TM2.stepAux (program (labels .initialize)) _ _) = _
    rw [atLabels, statement]
    simp [TM2.stepAux, started, ready.currentEmpty, encodeWord]
  have hsq : started (slots 0) = encodeWord q := by
    simpa [started, slots.injective.eq_iff] using ready.boundWord
  have hss : started (slots 3) = [] := by
    simpa [started, slots.injective.eq_iff] using ready.scratchEmpty
  have hr := MachineUnaryAffineAt.seededAffineTrace (slots 0) (slots 3) (slots 1)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
    (slots.injective.ne (by decide)) 1 1
    (labels (.remaining .seed)) (labels (.remaining .scan)) (labels (.remaining .restore))
    (some (labels (.closure .seed))) program
    (atLabels (.remaining .seed)) (atLabels (.remaining .scan)) (atLabels (.remaining .restore))
    started q [] (by simpa using hsq) hss (ambient, false) none
  have hrs : started (slots 1) = [] := by
    simpa [started, slots.injective.eq_iff] using ready.remainingEmpty
  simp only [Nat.one_mul, hrs, List.append_nil] at hr
  change (advance (TM2.step program))^[2 * (q + 1) + 1]
    (some ⟨some (labels (.remaining .seed)), clean ambient, started⟩) =
    some ⟨some (labels (.closure .seed)), clean ambient, remaining⟩ at hr
  have hrq : remaining (slots 0) = encodeWord q := by
    simpa [remaining, slots.injective.eq_iff] using hsq
  have hsc : remaining (slots 3) = [] := by
    simpa [remaining, slots.injective.eq_iff] using hss
  have hc := MachineUnaryAffineAt.seededAffineTrace (slots 0) (slots 3) (slots 4)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
    (slots.injective.ne (by decide)) 1 1
    (labels (.closure .seed)) (labels (.closure .scan)) (labels (.closure .restore))
    (some (labels (.selector .guard))) program
    (atLabels (.closure .seed)) (atLabels (.closure .scan)) (atLabels (.closure .restore))
    remaining q [] (by simpa using hrq) hsc (ambient, false) none
  have hrc : remaining (slots 4) = [] := by
    simpa [remaining, started, slots.injective.eq_iff] using ready.closureEmpty
  simp only [Nat.one_mul, hrc, List.append_nil] at hc
  change (advance (TM2.step program))^[2 * (q + 1) + 1]
    (some ⟨some (labels (.closure .seed)), clean ambient, remaining⟩) =
    some ⟨some (labels (.selector .guard)), clean ambient, prepared⟩ at hc
  let loopBase := Function.update base (slots 4) (encodeWord (q + 1))
  have hprepared : prepared = SelectorLoop.frame (loopMap.trans slots) loopBase (q + 1) 0 := by
    funext k
    by_cases h₁ : k = slots 1
    · subst k; simp [prepared, remaining, started, frame_updates, loopBase, slots.injective.eq_iff]
    · by_cases h₂ : k = slots 2
      · subst k; simp [prepared, remaining, started, frame_updates, loopBase, slots.injective.eq_iff]
      · by_cases h₄ : k = slots 4
        · subst k; simp [prepared, remaining, started, frame_updates, loopBase, slots.injective.eq_iff]
        · simp [prepared, remaining, started, frame_updates, loopBase, h₁, h₂, h₄]
  have hls : loopBase ((loopMap.trans slots) 2) = [] := by
    simpa [loopBase, loopMap, slots.injective.eq_iff] using ready.scratchEmpty
  have hl := SelectorLoop.trace (loopMap.trans slots) (fun l => labels (.selector l))
    (labels .orSeed) program (fun _ => atLabels _) loopBase (q + 1) 0 hls ambient
  let afterLoop := SelectorLoop.frame (loopMap.trans slots)
    (emitted (slots 5) (slots 6) loopBase (SelectorLoop.tokens (q + 1) 0)) 0 (q + 1)
  rw [Nat.zero_add] at hl
  change (advance (TM2.step program))^[SelectorLoop.steps (q + 1) 0]
    (some ⟨some (labels (.selector .guard)), clean ambient,
      SelectorLoop.frame (loopMap.trans slots) loopBase (q + 1) 0⟩) =
    some ⟨some (labels .orSeed), clean ambient, afterLoop⟩ at hl
  rw [← hprepared] at hl
  have hac : afterLoop (slots 4) = encodeWord (q + 1) := by
    simp [afterLoop, frame_updates, loopBase, emitted, slots.injective.eq_iff]
  have hstart : OrClosure.frame (closurePorts slots) afterLoop (encodeWord (q + 1) ++ [])
      (afterLoop (slots 5)) (afterLoop (slots 6)) = afterLoop := by
    rw [List.append_nil, ← hac]
    change OrClosure.frame (closurePorts slots) afterLoop
      (afterLoop (closurePorts slots).remaining) (afterLoop (closurePorts slots).reversed)
      (afterLoop (closurePorts slots).count) = afterLoop
    exact OrClosure.frame_self (closurePorts slots) afterLoop
  have ho := OrClosure.closureTrace (closurePorts slots) (labels .orSeed) (labels .orLoop)
    (some (labels .cleanup)) program (atLabels .orSeed) (atLabels .orLoop)
    afterLoop (q + 1) [] (afterLoop (slots 5)) (afterLoop (slots 6)) (ambient, false) none
  rw [hstart, List.append_nil] at ho
  have hclosed := closed_frame (closurePorts slots) afterLoop (q + 1)
  change OrClosure.frame (closurePorts slots) afterLoop (encodeWord 0)
      ((tokenBits (closeOr (q + 1))).reverse ++ afterLoop (slots 5))
      (List.replicate (q + 1 + 1) true ++ afterLoop (slots 6)) =
    emitted (slots 5) (slots 6) (Function.update afterLoop (slots 4) (encodeWord 0))
      (closeOr (q + 1)) at hclosed
  rw [hclosed] at ho
  let closed := emitted (slots 5) (slots 6)
    (Function.update afterLoop (slots 4) (encodeWord 0)) (closeOr (q + 1))
  change (advance (TM2.step program))^[q + 3]
    (some ⟨some (labels .orSeed), clean ambient, afterLoop⟩) =
    some ⟨some (labels .cleanup), clean ambient, closed⟩ at ho
  have hcr : closed (slots 1) = encodeWord 0 := by
    simp [closed, afterLoop, frame_updates, emitted, slots.injective.eq_iff]
  have hcc : closed (slots 4) = encodeWord 0 := by
    simp [closed, emitted, slots.injective.eq_iff]
  let cleared := Function.update (Function.update closed (slots 1) []) (slots 4) []
  have hcleanup : (advance (TM2.step program))^[1]
      (some ⟨some (labels .cleanup), clean ambient, closed⟩) =
      some ⟨some (labels .drain), clean ambient, cleared⟩ := by
    change some (TM2.stepAux (program (labels .cleanup)) _ _) = _
    rw [atLabels, statement]
    simp [TM2.stepAux, hcr, hcc, encodeWord, cleared, slots.injective.eq_iff]
  have hcur : cleared (slots 2) = encodeWord (q + 1) := by
    simp [cleared, closed, afterLoop, frame_updates, emitted, slots.injective.eq_iff]
  have hd := MachineDrain.drainTrace (slots 2) (labels .drain) exit program (atLabels .drain)
    cleared (encodeWord (q + 1)) (ambient, false) none
  rw [← hcur, Function.update_eq_self] at hd
  rw [hcur, encodeWord_length] at hd
  have hfinish : Function.update cleared (slots 2) [] =
      emitted (slots 5) (slots 6) base (nonemptyTokens q) := by
    have hmove (k : Fin 7) (hk₅ : k ≠ 5) (hk₆ : k ≠ 6)
        (b : K → List Bool) (word : List Bool) (ts : List Token) :=
      emitted_update (slots 5) (slots 6) (slots k)
        (slots.injective.ne hk₅) (slots.injective.ne hk₆) b word ts
    simp only [cleared, closed, afterLoop, frame_updates, loopBase,
      hmove 1 (by decide) (by decide), hmove 2 (by decide) (by decide),
      hmove 4 (by decide) (by decide),
      emitted_append (slots 5) (slots 6)
        (slots.injective.ne (by decide : (5 : Fin 7) ≠ 6)), tokens_nonempty]
    funext k
    by_cases h₁ : k = slots 1
    · subst k; simp [emitted, slots.injective.eq_iff, ready.remainingEmpty]
    · by_cases h₂ : k = slots 2
      · subst k; simp [emitted, slots.injective.eq_iff, ready.currentEmpty]
      · by_cases h₄ : k = slots 4
        · subst k; simp [emitted, slots.injective.eq_iff, ready.closureEmpty]
        · simp [h₁, h₂, h₄]
  rw [hfinish] at hd
  exact chain (chain (chain (chain (chain (chain hi hr) hc) hl) ho) hcleanup) hd

theorem steps_le (q : Nat) : steps q ≤ 20 * (q + 2) ^ 2 := by
  have h := SelectorLoop.steps_le (q + 1) 0
  simp only [Nat.zero_add] at h
  unfold steps
  nlinarith

def inTime (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : Ready slots base q) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .initialize), clean ambient, base⟩
      (some ⟨exit, clean ambient, emitted (slots 5) (slots 6) base (nonemptyTokens q)⟩)
      (20 * (q + 2) ^ 2) where
  steps := steps q
  evals_in_steps := by
    change (advance (TM2.step program))^[steps q] _ = _
    exact trace slots labels exit program atLabels base q ready ambient
  steps_le_m := steps_le q

variable [Fintype K] [Fintype σ]

def machine (slots : Fin 7 ↪ K) (ambient : σ) : FinTM2 where
  K := K
  k₀ := slots 0
  k₁ := slots 5
  Γ := Alphabet
  Λ := Label
  main := .initialize
  σ := State σ
  initialState := clean ambient
  Γk₀Fin := inferInstance
  m := statement slots id none

theorem machineTrace (slots : Fin 7 ↪ K) (base : K → List Bool) (q : Nat)
    (ready : Ready slots base q) (ambient : σ) :
    (advance (machine slots ambient).step)^[steps q]
      (some ⟨some .initialize, clean ambient, base⟩) =
      some ⟨none, clean ambient, emitted (slots 5) (slots 6) base (nonemptyTokens q)⟩ := by
  exact trace slots id none (machine slots ambient).m (fun _ => rfl) base q ready ambient

end Nonempty

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

end OAI
