import OAI.Computability.BinPacking.CookLevin.PaddingCellsMachine
import OAI.Computability.BinPacking.CookLevin.PayloadPresenceMachine

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted)
open PayloadPresenceMachine (Ports Ready)

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

private theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

structure SymbolSpec where
  isInput : Bool
  trueValue : Bool
  falseValue : Bool
  absentValue : Bool
  deriving DecidableEq, Fintype

def payloadTokens (address : Nat) (yes no : Bool) : List Token :=
  [.input address, .const yes, .and, .input address, .not, .const no, .and, .or]

def symbolTokens (spec : SymbolSpec) (q i : Nat) : List Token :=
  if spec.isInput then
    muxTokens (presenceTokens q i) (payloadTokens (q + 1 + i) spec.trueValue spec.falseValue)
      [.const spec.absentValue]
  else [.const spec.absentValue]

namespace Payload

def inputMap : Fin 4 ↪ Fin 9 := ⟨![3, 5, 7, 8], by decide⟩

inductive Label where
  | seed | scanQ | restoreQ | scanI | restoreI
  | inputTrue (l : ClashMachine.Input.Label)
  | middle
  | inputFalse (l : ClashMachine.Input.Label)
  | suffix | drain
  deriving DecidableEq, Fintype

def statement (slots : Ports K) (labels : Label → Λ) (exit : Option Λ) (yes no : Bool) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => MachineUnaryAffineAt.seed (slots 3) 1 (labels .scanQ)
  | .scanQ => MachineUnaryAffineAt.scan (slots 0) (slots 5) (slots 3) 1
      (labels .scanQ) (labels .restoreQ)
  | .restoreQ => Reduction.MachineTransfer.loopAt (slots 5) (slots 0) id false
      (labels .restoreQ) (some (labels .scanI))
  | .scanI => MachineUnaryAffineAt.scan (slots 1) (slots 5) (slots 3) 1
      (labels .scanI) (labels .restoreI)
  | .restoreI => Reduction.MachineTransfer.loopAt (slots 5) (slots 1) id false
      (labels .restoreI) (some (labels (.inputTrue .tag)))
  | .inputTrue l => ClashMachine.Input.statement (inputMap.trans slots)
      (fun l => labels (.inputTrue l)) (some (labels .middle)) l
  | .middle => ClashMachine.literal (slots 7) (slots 8) [.const yes, .and]
      (.goto fun _ => labels (.inputFalse .tag))
  | .inputFalse l => ClashMachine.Input.statement (inputMap.trans slots)
      (fun l => labels (.inputFalse l)) (some (labels .suffix)) l
  | .suffix => ClashMachine.literal (slots 7) (slots 8) [.not, .const no, .and, .or]
      (.goto fun _ => labels .drain)
  | .drain => MachineDrain.drain (slots 3) (labels .drain) exit

def addressSteps (q i : Nat) := (2 * (q + 1) + 1) + 2 * (i + 1)

theorem addressTrace (slots : Ports K) (labels : Label → Λ) (exit : Option Λ) (yes no : Bool)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit yes no l)
    (base : K → List Bool) (q i : Nat) (ready : Ready slots base q i) (ambient : σ) :
    (advance (TM2.step program))^[addressSteps q i]
      (some ⟨some (labels .seed), clean ambient, base⟩) =
      some ⟨some (labels (.inputTrue .tag)), clean ambient,
        Function.update base (slots 3) (encodeWord (q + 1 + i))⟩ := by
  have e₃ := ready.empty 3 (by decide) (by decide) (by decide) (by decide)
  have e₅ := ready.empty 5 (by decide) (by decide) (by decide) (by decide)
  have hq := MachineUnaryAffineAt.seededAffineTrace (slots 0) (slots 5) (slots 3)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
    (slots.injective.ne (by decide)) 1 1 (labels .seed) (labels .scanQ) (labels .restoreQ)
    (some (labels .scanI)) program (atLabels .seed) (atLabels .scanQ) (atLabels .restoreQ)
    base q [] (by simpa using ready.boundWord) e₅ (ambient, false) none
  simp only [Nat.one_mul, e₃, List.append_nil] at hq
  let addressed := Function.update base (slots 3) (encodeWord (q + 1))
  have hi := MachineUnaryAffineAt.affineTrace (slots 1) (slots 5) (slots 3)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
    (slots.injective.ne (by decide)) 1 (labels .scanI) (labels .restoreI)
    (some (labels (.inputTrue .tag))) program (atLabels .scanI) (atLabels .restoreI)
    addressed i (q + 1) [] [] (ambient, false) none
  have hframe (n : Nat) : MachineUnaryAffineAt.tapes (slots 1) (slots 5) (slots 3)
      addressed (encodeWord i ++ []) [] (encodeWord n ++ []) =
      Function.update base (slots 3) (encodeWord n) := by
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, List.append_nil]
    apply ClashMachine.Full.ext_slots slots
    · intro j
      fin_cases j <;> simp [addressed, slots.injective.eq_iff, ready.indexWord, e₅]
    · intro k hk
      simp [addressed, hk]
  rw [hframe, hframe] at hi
  rw [show 1 * i + (q + 1) = q + 1 + i by omega] at hi
  exact chain hq hi

def steps (q i : Nat) : Nat := addressSteps q i + ClashMachine.Input.steps (q + 1 + i) + 1 +
  ClashMachine.Input.steps (q + 1 + i) + 1 + (q + 1 + i + 2)

theorem trace (slots : Ports K) (labels : Label → Λ) (exit : Option Λ) (yes no : Bool)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit yes no l)
    (base : K → List Bool) (q i : Nat) (ready : Ready slots base q i) (ambient : σ) :
    (advance (TM2.step program))^[steps q i]
      (some ⟨some (labels .seed), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        emitted (slots 7) (slots 8) base (payloadTokens (q + 1 + i) yes no)⟩ := by
  have e₃ := ready.empty 3 (by decide) (by decide) (by decide) (by decide)
  have e₅ := ready.empty 5 (by decide) (by decide) (by decide) (by decide)
  let address := q + 1 + i
  let b₀ := Function.update base (slots 3) (encodeWord address)
  have ha := addressTrace slots labels exit yes no program atLabels base q i ready ambient
  have ht := ClashMachine.Input.trace (inputMap.trans slots) (fun l => labels (.inputTrue l))
    (some (labels .middle)) program (fun _ => atLabels _) b₀ address
    (by simp [b₀, inputMap]) (by simpa [b₀, inputMap, slots.injective.eq_iff] using e₅) ambient
  let b₁ := emitted (slots 7) (slots 8) b₀ [.input address]
  have hm : (advance (TM2.step program))^[1]
      (some ⟨some (labels .middle), clean ambient, b₁⟩) =
      some ⟨some (labels (.inputFalse .tag)), clean ambient,
        emitted (slots 7) (slots 8) b₁ [.const yes, .and]⟩ := by
    change some (TM2.stepAux (program (labels .middle)) _ _) = _
    rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
    rfl
  let b₂ := emitted (slots 7) (slots 8) b₁ [.const yes, .and]
  have hf := ClashMachine.Input.trace (inputMap.trans slots) (fun l => labels (.inputFalse l))
    (some (labels .suffix)) program (fun _ => atLabels _) b₂ address
    (by simp [b₂, b₁, b₀, inputMap, emitted, slots.injective.eq_iff])
    (by simpa [b₂, b₁, b₀, inputMap, emitted, slots.injective.eq_iff] using e₅) ambient
  let b₃ := emitted (slots 7) (slots 8) b₂ [.input address]
  have hs : (advance (TM2.step program))^[1]
      (some ⟨some (labels .suffix), clean ambient, b₃⟩) =
      some ⟨some (labels .drain), clean ambient,
        emitted (slots 7) (slots 8) b₃ [.not, .const no, .and, .or]⟩ := by
    change some (TM2.stepAux (program (labels .suffix)) _ _) = _
    rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
    rfl
  let b₄ := emitted (slots 7) (slots 8) b₃ [.not, .const no, .and, .or]
  have hword : b₄ (slots 3) = encodeWord address := by
    simp [b₄, b₃, b₂, b₁, b₀, emitted, slots.injective.eq_iff]
  have hd := MachineDrain.drainTrace (slots 3) (labels .drain) exit program (atLabels .drain)
    b₄ (encodeWord address) (ambient, false) none
  rw [← hword, Function.update_eq_self] at hd
  rw [hword, encodeWord_length] at hd
  have hfinish : Function.update b₄ (slots 3) [] =
      emitted (slots 7) (slots 8) base (payloadTokens address yes no) := by
    have hb : b₄ = emitted (slots 7) (slots 8) b₀ (payloadTokens address yes no) := by
      simp only [b₄, b₃, b₂, b₁, ClashMachine.emitted_append (slots 7) (slots 8)
        (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
      rfl
    rw [hb]
    apply ClashMachine.Full.ext_slots slots
    · intro j
      fin_cases j <;> simp [b₀, emitted, slots.injective.eq_iff, e₃]
    · intro k hk
      simp [b₀, emitted, hk]
  rw [hfinish] at hd
  exact chain (chain (chain (chain (chain ha ht) hm) hf) hs) hd

theorem steps_le (q i : Nat) (hi : i < q) : steps q i ≤ 40 * (q + 2) := by
  unfold steps addressSteps ClashMachine.Input.steps
  omega

end Payload

namespace Symbol

inductive Label where
  | start
  | first (l : PayloadPresenceMachine.Label)
  | payload (l : Payload.Label)
  | conjunction
  | second (l : PayloadPresenceMachine.Label)
  | suffix
  deriving DecidableEq, Fintype

def firstLabels : PayloadPresenceMachine.Label ↪ Label := ⟨.first, fun _ _ h => by cases h; rfl⟩
def secondLabels : PayloadPresenceMachine.Label ↪ Label := ⟨.second, fun _ _ h => by cases h; rfl⟩

def statement (slots : Ports K) (labels : Label ↪ Λ) (exit : Option Λ) (spec : SymbolSpec) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => if spec.isInput then .goto fun _ => labels (.first .initialize)
      else ClashMachine.literal (slots 7) (slots 8) [.const spec.absentValue]
        (Reduction.MachineTransfer.exitAt (slots 7) exit)
  | .first l => PayloadPresenceMachine.statement slots (firstLabels.trans labels)
      (some (labels (.payload .seed))) l
  | .payload l => Payload.statement slots (fun l => labels (.payload l))
      (some (labels .conjunction)) spec.trueValue spec.falseValue l
  | .conjunction => ClashMachine.literal (slots 7) (slots 8) [.and]
      (.goto fun _ => labels (.second .initialize))
  | .second l => PayloadPresenceMachine.statement slots (secondLabels.trans labels)
      (some (labels .suffix)) l
  | .suffix => ClashMachine.literal (slots 7) (slots 8) [.not, .const spec.absentValue, .and, .or]
      (Reduction.MachineTransfer.exitAt (slots 7) exit)

def steps (spec : SymbolSpec) (q i : Nat) : Nat :=
  if spec.isInput then
    1 + PayloadPresenceMachine.steps q i + Payload.steps q i + 1 + PayloadPresenceMachine.steps q i + 1
  else 1

theorem trace (slots : Ports K) (labels : Label ↪ Λ) (exit : Option Λ) (spec : SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit spec l)
    (base : K → List Bool) (q i : Nat) (hi : i < q)
    (ready : Ready slots base q i) (ambient : σ) :
    (advance (TM2.step program))^[steps spec q i]
      (some ⟨some (labels .start), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (symbolTokens spec q i)⟩ := by
  cases hspec : spec.isInput with
  | false =>
    simp only [steps, hspec, Bool.false_eq_true, ↓reduceIte]
    change some (TM2.stepAux (program (labels .start)) _ _) = _
    rw [atLabels, statement, hspec]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ClashMachine.stepAux_literal (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
    cases exit <;> simp [Reduction.MachineTransfer.exitAt, TM2.stepAux, symbolTokens, hspec]
  | true =>
    have hs : (advance (TM2.step program))^[1]
        (some ⟨some (labels .start), clean ambient, base⟩) =
        some ⟨some (labels (.first .initialize)), clean ambient, base⟩ := by
      change some (TM2.stepAux (program (labels .start)) _ _) = _
      rw [atLabels, statement, hspec]
      rfl
    have h₁ := PayloadPresenceMachine.trace slots (firstLabels.trans labels)
      (some (labels (.payload .seed))) program (fun _ => atLabels _) base q i hi ready ambient
    let b₁ := emitted (slots 7) (slots 8) base (presenceTokens q i)
    have hp := Payload.trace slots (fun l => labels (.payload l)) (some (labels .conjunction))
      spec.trueValue spec.falseValue program (fun _ => atLabels _)
      b₁ q i (ready.emitted (presenceTokens q i)) ambient
    let b₂ := emitted (slots 7) (slots 8) b₁ (payloadTokens (q + 1 + i) spec.trueValue spec.falseValue)
    have hc : (advance (TM2.step program))^[1]
        (some ⟨some (labels .conjunction), clean ambient, b₂⟩) =
        some ⟨some (labels (.second .initialize)), clean ambient,
          emitted (slots 7) (slots 8) b₂ [.and]⟩ := by
      change some (TM2.stepAux (program (labels .conjunction)) _ _) = _
      rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
        (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
      rfl
    let b₃ := emitted (slots 7) (slots 8) b₂ [.and]
    have r₃ : Ready slots b₃ q i :=
      ((ready.emitted (presenceTokens q i)).emitted
        (payloadTokens (q + 1 + i) spec.trueValue spec.falseValue)).emitted [.and]
    have h₂ := PayloadPresenceMachine.trace slots (secondLabels.trans labels)
      (some (labels .suffix)) program (fun _ => atLabels _) b₃ q i hi r₃ ambient
    let b₄ := emitted (slots 7) (slots 8) b₃ (presenceTokens q i)
    have hf : (advance (TM2.step program))^[1]
        (some ⟨some (labels .suffix), clean ambient, b₄⟩) =
        some ⟨exit, clean ambient,
          emitted (slots 7) (slots 8) b₄ [.not, .const spec.absentValue, .and, .or]⟩ := by
      change some (TM2.stepAux (program (labels .suffix)) _ _) = _
      rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
        (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
      cases exit <;> rfl
    have h := chain (chain (chain (chain (chain hs h₁) hp) hc) h₂) hf
    simpa only [steps, hspec, ↓reduceIte, b₄, b₃, b₂, b₁,
      ClashMachine.emitted_append (slots 7) (slots 8)
        (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8)), symbolTokens, muxTokens,
      List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using h

theorem steps_le (spec : SymbolSpec) (q i : Nat) (hi : i < q) :
    steps spec q i ≤ 120 * (q + 2) ^ 2 := by
  have hq : q + 2 ≤ (q + 2) ^ 2 := by nlinarith
  have hp := Payload.steps_le q i hi
  have hc := PayloadPresenceMachine.steps_le q i hi
  unfold steps
  split <;> omega

end Symbol

namespace Row

variable {A : Nat}

def tableAt (table : Fin A → SymbolSpec) (j : Nat) : SymbolSpec :=
  if hj : j < A then table ⟨j, hj⟩ else ⟨false, false, false, false⟩

def tokensFrom (table : Fin A → SymbolSpec) (q i start count : Nat) : List Token :=
  forTokens count (fun j => symbolTokens (tableAt table (start + j)) q i)

def tokens (table : Fin A → SymbolSpec) (q i : Nat) : List Token := tokensFrom table q i 0 A

theorem tokensFrom_succ (table : Fin A → SymbolSpec) (q i start count : Nat) :
    tokensFrom table q i start (count + 1) =
      symbolTokens (tableAt table start) q i ++ tokensFrom table q i (start + 1) count := by
  rw [tokensFrom, forTokens_succ_first]
  simp only [Nat.add_zero]
  apply congrArg (List.append (symbolTokens (tableAt table start) q i))
  apply forTokens_congr
  intro j _
  rw [show start + (j + 1) = start + 1 + j by omega]

theorem tokens_eq_ofFn (table : Fin A → SymbolSpec) (q i : Nat) :
    tokens table q i = (List.ofFn fun j : Fin A => symbolTokens (table j) q i).flatten := by
  rw [tokens, tokensFrom, forTokens_eq_ofFn]
  congr 1
  congr 1
  funext j
  simp [tableAt, j.isLt]

inductive Label (A : Nat) where
  | visit (j : Fin (A + 1))
  | symbol (j : Fin A) (l : Symbol.Label)
  deriving DecidableEq, Fintype

def symbolLabels (j : Fin A) : Symbol.Label ↪ Label A :=
  ⟨Label.symbol j, fun _ _ h => by cases h; rfl⟩

def statement (slots : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (table : Fin A → SymbolSpec) : Label A → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .visit j => if hj : j.val < A then .goto fun _ => labels (.symbol ⟨j.val, hj⟩ .start)
      else Reduction.MachineTransfer.exitAt (slots 7) exit
  | .symbol j l => Symbol.statement slots ((symbolLabels j).trans labels)
      (some (labels (.visit ⟨j.val + 1, by omega⟩))) (table j) l

def stepsFrom (table : Fin A → SymbolSpec) (q i : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | start, count + 1 => 1 + Symbol.steps (tableAt table start) q i + stepsFrom table q i (start + 1) count

def steps (table : Fin A → SymbolSpec) (q i : Nat) : Nat := stepsFrom table q i 0 A

theorem traceFrom (slots : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit table l)
    (base : K → List Bool) (q i : Nat) (hi : i < q) (ready : Ready slots base q i)
    (ambient : σ) (start count : Nat) (hfinish : start + count = A) :
    (advance (TM2.step program))^[stepsFrom table q i start count]
      (some ⟨some (labels (.visit ⟨start, by omega⟩)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (tokensFrom table q i start count)⟩ := by
  induction count generalizing start base with
  | zero =>
    have hstart : start = A := by omega
    change some (TM2.stepAux (program (labels (.visit ⟨start, by omega⟩))) _ _) = _
    rw [atLabels, statement, dite_eq_right (show ¬ start < A by omega)]
    cases exit <;> simp [TM2.stepAux, Reduction.MachineTransfer.exitAt,
      tokensFrom, forTokens, ClashMachine.emitted_nil]
  | succ count ih =>
    have hstart : start < A := by omega
    let j : Fin A := ⟨start, hstart⟩
    have hv : (advance (TM2.step program))^[1]
        (some ⟨some (labels (.visit ⟨start, by omega⟩)), clean ambient, base⟩) =
        some ⟨some (labels (.symbol j .start)), clean ambient, base⟩ := by
      change some (TM2.stepAux (program (labels (.visit ⟨start, by omega⟩))) _ _) = _
      rw [atLabels, statement, dite_eq_left hstart]
      rfl
    have hs := Symbol.trace slots ((symbolLabels j).trans labels)
      (some (labels (.visit ⟨start + 1, by omega⟩))) (table j) program
      (fun l => atLabels (.symbol j l)) base q i hi ready ambient
    let nextBase := emitted (slots 7) (slots 8) base (symbolTokens (table j) q i)
    have hn := ih nextBase (ready.emitted (symbolTokens (table j) q i)) (start + 1) (by omega)
    have h := chain (chain hv hs) hn
    have ht : tableAt table start = table j := dite_eq_left hstart
    simpa only [stepsFrom, tokensFrom_succ, ht, nextBase,
      ClashMachine.emitted_append (slots 7) (slots 8)
        (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))] using h

theorem trace (slots : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit table l)
    (base : K → List Bool) (q i : Nat) (hi : i < q) (ready : Ready slots base q i) (ambient : σ) :
    (advance (TM2.step program))^[steps table q i]
      (some ⟨some (labels (.visit 0)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (tokens table q i)⟩ := by
  exact traceFrom slots labels exit table program atLabels base q i hi ready ambient 0 A (by omega)

theorem stepsFrom_le (table : Fin A → SymbolSpec) (q i start count : Nat) (hi : i < q) :
    stepsFrom table q i start count ≤ count * (120 * (q + 2) ^ 2 + 1) + 1 := by
  induction count generalizing start with
  | zero => simp [stepsFrom]
  | succ count ih =>
    have hs := Symbol.steps_le (tableAt table start) q i hi
    have hr := ih (start + 1)
    rw [stepsFrom, Nat.succ_mul]
    omega

theorem steps_le (table : Fin A → SymbolSpec) (q i : Nat) (hi : i < q) :
    steps table q i ≤ A * (120 * (q + 2) ^ 2 + 1) + 1 := stepsFrom_le table q i 0 A hi

def inTime (slots : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit table l)
    (base : K → List Bool) (q i : Nat) (hi : i < q) (ready : Ready slots base q i) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.visit 0)), clean ambient, base⟩
      (some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (tokens table q i)⟩)
      (A * (120 * (q + 2) ^ 2 + 1) + 1) where
  steps := steps table q i
  evals_in_steps := by
    change (advance (TM2.step program))^[steps table q i] _ = _
    exact trace slots labels exit table program atLabels base q i hi ready ambient
  steps_le_m := steps_le table q i hi

variable [Fintype K] [Fintype σ]

def machine (slots : Ports K) (table : Fin A → SymbolSpec) (ambient : σ) : FinTM2 where
  K := K
  k₀ := slots 0
  k₁ := slots 7
  Γ := Alphabet
  Λ := Label A
  main := .visit 0
  σ := State σ
  initialState := clean ambient
  Γk₀Fin := inferInstance
  m := statement slots (Function.Embedding.refl _) none table

def machineInTime (slots : Ports K) (table : Fin A → SymbolSpec)
    (base : K → List Bool) (q i : Nat) (hi : i < q)
    (ready : Ready slots base q i) (ambient : σ) :
    StateTransition.EvalsToInTime (machine slots table ambient).step
      ⟨some (.visit 0), clean ambient, base⟩
      (some ⟨none, clean ambient, emitted (slots 7) (slots 8) base (tokens table q i)⟩)
      (A * (120 * (q + 2) ^ 2 + 1) + 1) :=
  inTime slots (Function.Embedding.refl _) none table (machine slots table ambient).m
    (fun _ => rfl) base q i hi ready ambient

end Row

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadRowsLoop

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted emitted_append)
open PayloadCellsMachine (SymbolSpec)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev Ports (K : Type) := Fin 11 ↪ K
abbrev Alphabet (_ : K) := Bool

def rowMap : Fin 9 ↪ Fin 11 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)

def rowPorts (p : Ports K) : PayloadPresenceMachine.Ports K := rowMap.trans p

def frame (p : Ports K) (base : K → List Bool) (remaining index capacity : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base (p 1) (encodeWord index))
    (p 9) (encodeWord remaining)) (p 10) (encodeWord capacity)

@[simp] theorem frame_index (p : Ports K) (base : K → List Bool) (m i c : Nat) :
    frame p base m i c (p 1) = encodeWord i := by simp [frame, p.injective.eq_iff]

@[simp] theorem frame_remaining (p : Ports K) (base : K → List Bool) (m i c : Nat) :
    frame p base m i c (p 9) = encodeWord m := by simp [frame, p.injective.eq_iff]

@[simp] theorem frame_capacity (p : Ports K) (base : K → List Bool) (m i c : Nat) :
    frame p base m i c (p 10) = encodeWord c := by simp [frame]

private theorem ext_ports (p : Ports K) {f g : K → List Bool}
    (atPorts : ∀ j, f (p j) = g (p j))
    (outside : ∀ k, (∀ j, k ≠ p j) → f k = g k) : f = g := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    exact atPorts j
  · exact outside k (fun j h => hk ⟨j, h.symm⟩)

theorem update_remaining (p : Ports K) (base : K → List Bool) (m i c r : Nat) :
    Function.update (frame p base m i c) (p 9) (encodeWord r) = frame p base r i c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, p.injective.eq_iff]
  · intro k hk
    simp [frame, hk]

theorem update_index (p : Ports K) (base : K → List Bool) (m i c r : Nat) :
    Function.update (frame p base m i c) (p 1) (encodeWord r) = frame p base m r c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, p.injective.eq_iff]
  · intro k hk
    simp [frame, hk]

theorem update_capacity (p : Ports K) (base : K → List Bool) (m i c r : Nat) :
    Function.update (frame p base m i c) (p 10) (encodeWord r) = frame p base m i r := by
  simp [frame]

theorem frame_emitted (p : Ports K) (base : K → List Bool) (m i c : Nat) (tokens : List Token) :
    emitted (p 7) (p 8) (frame p base m i c) tokens =
      frame p (emitted (p 7) (p 8) base tokens) m i c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, emitted, p.injective.eq_iff]
  · intro k hk
    simp [frame, emitted, hk]

theorem frame_ready (p : Ports K) (base : K → List Bool) (q m i c : Nat)
    (ready : PayloadPresenceMachine.Ready (rowPorts p) base q 0) :
    PayloadPresenceMachine.Ready (rowPorts p) (frame p base m i c) q i := by
  constructor
  · change frame p base m i c (p 0) = encodeWord q
    have boundWord : base (p 0) = encodeWord q := ready.boundWord
    simpa [frame, p.injective.eq_iff] using boundWord
  · exact frame_index p base m i c
  · intro j h₀ h₁ h₇ h₈
    have h1 : rowMap j ≠ (1 : Fin 11) := by
      intro h
      apply h₁
      exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)
    have h9 : rowMap j ≠ (9 : Fin 11) := by
      intro h
      have hv := congrArg (fun x : Fin 11 => x.val) h
      change j.val = 9 at hv
      omega
    have h10 : rowMap j ≠ (10 : Fin 11) := by
      intro h
      have hv := congrArg (fun x : Fin 11 => x.val) h
      change j.val = 10 at hv
      omega
    simpa only [rowPorts, Function.Embedding.trans_apply, frame,
      Function.update_of_ne (p.injective.ne h10), Function.update_of_ne (p.injective.ne h9),
      Function.update_of_ne (p.injective.ne h1)] using ready.empty j h₀ h₁ h₇ h₈

inductive Label (symbols : Nat)
  | guard | next
  | row (entry : PayloadCellsMachine.Row.Label symbols)
  deriving DecidableEq, Fintype

def rowLabels (label : Label A ↪ Λ) : PayloadCellsMachine.Row.Label A ↪ Λ where
  toFun entry := label (.row entry)
  inj' := by intro i j h; exact Label.row.inj (label.injective h)

def statement (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) : Label A → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .guard => MachineUnaryCounter.guard (p 9) (label (.row (.visit 0))) exit
  | .next => .pop (p 10) (fun state _ => state)
      (.push (p 1) (fun _ => true) (.goto fun _ => label .guard))
  | .row entry => PayloadCellsMachine.Row.statement (rowPorts p) (rowLabels label)
      (some (label .next)) table entry

def Agrees (p : Ports K) (label : Label A ↪ Λ) (exit : Λ) (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) : Prop :=
  ∀ entry, program (label entry) = statement p label exit table entry

theorem guardStep_zero (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (i c : Nat) (ambient : σ) :
    TM2.step program ⟨some (label .guard), clean ambient, frame p base 0 i c⟩ =
      some ⟨some exit, clean ambient, frame p base 0 i c⟩ := by
  change some (TM2.stepAux (program (label .guard)) _ _) = _
  rw [ha .guard]
  simp [statement, MachineUnaryCounter.guard, TM2.stepAux, clean, encodeWord]

theorem guardStep_succ (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (m i c : Nat) (ambient : σ) :
    TM2.step program ⟨some (label .guard), clean ambient, frame p base (m + 1) i c⟩ =
      some ⟨some (label (.row (.visit 0))), clean ambient, frame p base m i c⟩ := by
  change some (TM2.stepAux (program (label .guard)) _ _) = _
  rw [ha .guard]
  simp [statement, MachineUnaryCounter.guard, TM2.stepAux, clean, encodeWord, List.replicate_succ]
  exact update_remaining p base (m + 1) i c m

theorem nextStep (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (m i c : Nat) (ambient : σ) :
    TM2.step program ⟨some (label .next), clean ambient, frame p base m i (c + 1)⟩ =
      some ⟨some (label .guard), clean ambient, frame p base m (i + 1) c⟩ := by
  change some (TM2.stepAux (program (label .next)) _ _) = _
  rw [ha .next]
  simp only [statement, TM2.stepAux, frame_capacity, encodeWord, List.replicate_succ,
    List.cons_append, List.tail_cons]
  rw [Function.update_of_ne (p.injective.ne (by decide : (1 : Fin 11) ≠ 10))]
  change some (⟨some (label .guard), clean ambient,
    Function.update (Function.update (frame p base m i (c + 1)) (p 10) (encodeWord c))
      (p 1) (true :: frame p base m i (c + 1) (p 1))⟩ : TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
  rw [update_capacity, frame_index]
  rw [show true :: encodeWord i = encodeWord (i + 1) by simp [encodeWord, List.replicate_succ]]
  rw [update_index]

def tokens (table : Fin A → SymbolSpec) (q : Nat) : Nat → Nat → List Token
  | _, 0 => []
  | i, m + 1 => PayloadCellsMachine.Row.tokens table q i ++ tokens table q (i + 1) m

def steps (table : Fin A → SymbolSpec) (q : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | i, m + 1 => 1 + PayloadCellsMachine.Row.steps table q i + 1 + steps table q (i + 1) m

theorem trace (p : Ports K) (label : Label A ↪ Λ) (exit : Λ) (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (q i m c : Nat)
    (hbound : i + m ≤ q) (ready : PayloadPresenceMachine.Ready (rowPorts p) base q 0)
    (ambient : σ) :
    (advance (TM2.step program))^[steps table q i m]
      (some ⟨some (label .guard), clean ambient, frame p base m i (c + m)⟩) =
      some ⟨some exit, clean ambient,
        emitted (p 7) (p 8) (frame p base 0 (i + m) c) (tokens table q i m)⟩ := by
  induction m generalizing base i with
  | zero =>
    simpa only [steps, Function.iterate_one, advance_some, Nat.add_zero,
      tokens, ClashMachine.emitted_nil] using guardStep_zero p label exit table program ha base i c ambient
  | succ m ih =>
    have hi : i < q := by omega
    have hguard : (advance (TM2.step program))^[1]
        (some ⟨some (label .guard), clean ambient, frame p base (m + 1) i (c + (m + 1))⟩) =
        some ⟨some (label (.row (.visit 0))), clean ambient, frame p base m i (c + (m + 1))⟩ := by
      simpa only [Function.iterate_one, advance_some] using
        guardStep_succ p label exit table program ha base m i (c + (m + 1)) ambient
    have hrow := PayloadCellsMachine.Row.trace (rowPorts p) (rowLabels label)
      (some (label .next)) table program (fun entry => ha (.row entry))
      (frame p base m i (c + (m + 1))) q i hi (frame_ready p base q m i _ ready) ambient
    change (advance (TM2.step program))^[PayloadCellsMachine.Row.steps table q i]
      (some ⟨some (label (.row (.visit 0))), clean ambient, frame p base m i (c + (m + 1))⟩) =
      some ⟨some (label .next), clean ambient,
        emitted (p 7) (p 8) (frame p base m i (c + (m + 1)))
          (PayloadCellsMachine.Row.tokens table q i)⟩ at hrow
    rw [frame_emitted] at hrow
    let nextBase := emitted (p 7) (p 8) base (PayloadCellsMachine.Row.tokens table q i)
    have hnext : (advance (TM2.step program))^[1]
        (some ⟨some (label .next), clean ambient, frame p nextBase m i (c + (m + 1))⟩) =
        some ⟨some (label .guard), clean ambient, frame p nextBase m (i + 1) (c + m)⟩ := by
      simpa only [Function.iterate_one, advance_some, Nat.add_assoc] using
        nextStep p label exit table program ha nextBase m i (c + m) ambient
    have hn : PayloadPresenceMachine.Ready (rowPorts p) nextBase q 0 :=
      ready.emitted (PayloadCellsMachine.Row.tokens table q i)
    have htail := ih nextBase (i + 1) (by omega) hn
    have h := ClashMachine.chain (ClashMachine.chain (ClashMachine.chain hguard hrow) hnext) htail
    have hend : i + 1 + m = i + (m + 1) := by omega
    simpa only [steps, tokens, hend, nextBase, ← frame_emitted,
      emitted_append (p 7) (p 8) (p.injective.ne (by decide : (7 : Fin 11) ≠ 8))] using h

theorem steps_le (table : Fin A → SymbolSpec) (q i m : Nat) (hbound : i + m ≤ q) :
    steps table q i m ≤ m * (A * (120 * (q + 2) ^ 2 + 1) + 3) + 1 := by
  induction m generalizing i with
  | zero => simp [steps]
  | succ m ih =>
    have ht := ih (i + 1) (by omega)
    have hr := PayloadCellsMachine.Row.steps_le table q i (by omega)
    rw [steps, Nat.succ_mul]
    omega

theorem tokens_eq_forTokens (table : Fin A → SymbolSpec) (q i m : Nat) :
    tokens table q i m = forTokens m (fun j => PayloadCellsMachine.Row.tokens table q (i + j)) := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    rw [tokens, forTokens_succ_first, Nat.add_zero, ih]
    apply congrArg (List.append (PayloadCellsMachine.Row.tokens table q i))
    apply forTokens_congr
    intro j _
    rw [show i + 1 + j = i + (j + 1) by omega]

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadRowsLoop

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

open InitializationTemplate WitnessEncoding

local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def symbolSpec (V : NPVerifier) (k : V.computation.tm.K)
    (a : Option (V.computation.tm.Γ k)) : SymbolSpec :=
  if h : k = V.computation.tm.k₀ then by
    subst k
    exact ⟨true, decide (some (V.computation.inputAlphabet.invFun true) = a),
      decide (some (V.computation.inputAlphabet.invFun false) = a), decide (none = a)⟩
  else ⟨false, false, false, decide (none = a)⟩

def symbolTable (V : NPVerifier) : Fin (VerifierCircuit.indexing V).symbolCount → SymbolSpec :=
  fun j => let symbol := (VerifierCircuit.indexing V).symbols.symm j
    symbolSpec V symbol.1 symbol.2

def payloadRowTokens (V : NPVerifier) (q i : Nat) : List PostfixModel.Token :=
  Row.tokens (symbolTable V) q i

theorem symbolTokens_eq_initialCellTokens (V : NPVerifier) (input : List Bool) (S i : Nat)
    (hi : i < V.witnessBound.eval input.length)
    (hS : (inputPrefix input).length + i < S) (k : V.computation.tm.K)
    (a : Option (V.computation.tm.Γ k)) :
    symbolTokens (symbolSpec V k a) (V.witnessBound.eval input.length) i =
      initialCellTokens V input S k ⟨(inputPrefix input).length + i, hS⟩ a := by
  by_cases hk : k = V.computation.tm.k₀
  · subst k
    have hp : ¬ (inputPrefix input).length + i < (inputPrefix input).length := by omega
    have hn : (inputPrefix input).length + i - (inputPrefix input).length = i := by omega
    have hcell : inputCellTokens (V.witnessBound.eval input.length) input
        V.computation.inputAlphabet.invFun ((inputPrefix input).length + i) a =
        muxTokens (presenceTokens (V.witnessBound.eval input.length) i)
          (payloadSymbolTokens (V.witnessBound.eval input.length)
            V.computation.inputAlphabet.invFun i a) [.const (decide (none = a))] := by
      simp only [inputCellTokens, ite_eq_right hp, hn, ite_eq_left hi]
    simpa [symbolTokens, symbolSpec, initialCellTokens, payloadTokens, payloadSymbolTokens] using hcell.symm
  · simp [symbolSpec, symbolTokens, initialCellTokens, hk]

theorem payloadRowTokens_eq (V : NPVerifier) (input : List Bool) (S i : Nat)
    (hi : i < V.witnessBound.eval input.length) (hS : (inputPrefix input).length + i < S) :
    payloadRowTokens V (V.witnessBound.eval input.length) i =
      (List.ofFn fun j : Fin (VerifierCircuit.indexing V).symbolCount =>
        let symbol := (VerifierCircuit.indexing V).symbols.symm j
        initialCellTokens V input S symbol.1 ⟨(inputPrefix input).length + i, hS⟩ symbol.2).flatten := by
  rw [payloadRowTokens, Row.tokens_eq_ofFn]
  congr 1
  congr 1
  funext j
  exact symbolTokens_eq_initialCellTokens V input S i hi hS _ _

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.CellsTokensAlignment

open WitnessEncoding InitializationTemplate PaddingCellsMachine

local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

theorem cellsInterval_append (V : NPVerifier) (input : List Bool) (S start m n : Nat)
    (within : start + (m + n) ≤ S) :
    cellsInterval V input S start (m + n) within =
      cellsInterval V input S start m (by omega) ++
        cellsInterval V input S (start + m) n (by omega) := by
  simp only [cellsInterval, List.flatMap_def, ← List.ofFn_eq_map]
  rw [List.ofFn_add, List.flatten_append]
  simp only [Fin.val_castLE, Fin.val_natAdd, Nat.add_assoc]

theorem cellsInterval_full (V : NPVerifier) (input : List Bool) (S : Nat) :
    cellsInterval V input S 0 S (by omega) = InitializationControl.cells V input S := by
  simp only [cellsInterval, InitializationControl.cells, Nat.zero_add]

theorem prefix_eq_interval (V : NPVerifier) (input : List Bool) (S : Nat)
    (within : (inputPrefix input).length ≤ S) :
    InputCellsMachine.streamTokens (InputCellsMachine.prefixTruth V) (inputPrefix input) =
      cellsInterval V input S 0 (inputPrefix input).length (by omega) := by
  simpa only [cellsInterval, List.flatMap_def, ← List.ofFn_eq_map, Nat.zero_add] using
    InputCellsMachine.prefixStream_eq_initialCells V input S within

theorem payload_eq_interval (V : NPVerifier) (input : List Bool) (S : Nat)
    (within : (inputPrefix input).length + V.witnessBound.eval input.length ≤ S) :
    PayloadRowsLoop.tokens (PayloadCellsMachine.symbolTable V)
      (V.witnessBound.eval input.length) 0 (V.witnessBound.eval input.length) =
      cellsInterval V input S (inputPrefix input).length (V.witnessBound.eval input.length) within := by
  rw [PayloadRowsLoop.tokens_eq_forTokens, forTokens_eq_ofFn]
  simp only [cellsInterval, List.flatMap_def, ← List.ofFn_eq_map, Nat.zero_add]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact PayloadCellsMachine.payloadRowTokens_eq V input S i.val i.isLt (by omega)

theorem cells_eq_streams (V : NPVerifier) (input : List Bool) (S : Nat)
    (within : (inputPrefix input).length + V.witnessBound.eval input.length ≤ S) :
    InputCellsMachine.streamTokens (InputCellsMachine.prefixTruth V) (inputPrefix input) ++
      PayloadRowsLoop.tokens (PayloadCellsMachine.symbolTable V)
        (V.witnessBound.eval input.length) 0 (V.witnessBound.eval input.length) ++
      repeatedRows (blankRow V)
        (S - (inputPrefix input).length - V.witnessBound.eval input.length) =
      InitializationControl.cells V input S := by
  let P := (inputPrefix input).length
  let q := V.witnessBound.eval input.length
  let r := S - P - q
  have hpq : P + q ≤ S := within
  have total : (P + q) + r = S := by dsimp only [r]; omega
  have hpre := prefix_eq_interval V input S (by omega)
  have hpay := payload_eq_interval V input S within
  have hpad := cellsInterval_padding V input S (P + q) r (by omega) (by exact le_rfl)
  rw [hpre, hpay, ← hpad]
  have first := cellsInterval_append V input S 0 P q (by omega)
  have second := cellsInterval_append V input S 0 (P + q) r (by omega)
  simp only [Nat.zero_add] at first second
  rw [← first, ← second]
  simpa only [total] using cellsInterval_full V input S

end BinPackingGames.Foundations.Complexity.CookLevin.CellsTokensAlignment

end

end OAI
