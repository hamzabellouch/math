import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedLoop
import OAI.Analysis.MatrixSigning.Encoding.BinaryEncoding

namespace OAI

namespace KS.W11.FramedArray
open KS.W01.FixedStack
open KS.W29 (StackAction)
open KS.W29.FixedSequential

def «stacks» (input output scratch index : List Bool) : Fin 4 → List Bool :=
  fun j => if j = 0 then input else if j = 1 then output else if j = 2 then scratch else index

def config {q : ℕ} (state : Option (Fin q)) (input output scratch index : List Bool) :
    Config 4 q := ⟨state, «stacks» input output scratch index⟩

theorem config_ext {q : ℕ} {c d : Config 4 q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

def skipDispatch (s : Fin 2) (heads : Fin 4 → Fin 3) (_coin : Bool) : Instruction 4 2 :=
  if (heads 0).val = 0 then Instruction.halt 4 2 else
    ⟨if s = 0 then (if (heads 0).val = 2 then none else some 1) else some 0,
      Vector.ofFn (fun j => if j = 0 then .pop else .stay)⟩

def skipMachine : Machine := compile 0 0 1 skipDispatch
def skipProgram : Program 4 := ofMachine skipMachine

@[simp] theorem skipProgram_toMachine : skipProgram.toMachine = skipMachine :=
  toMachine_ofMachine skipMachine

theorem roundtrip_step (M : Machine) (c : Config M.stackCount M.states) (coin : Bool) :
    (ofMachine M).toMachine.step c coin = M.step c coin := by
  cases M
  rfl

theorem roundtrip_run (M : Machine) (c : Config M.stackCount M.states) (bits : List Bool) :
    (ofMachine M).toMachine.run c bits = M.run c bits := by
  cases M
  rfl

theorem skipProgram_step (c : Config 4 2) (coin : Bool) :
    skipProgram.toMachine.step c coin = skipMachine.step c coin :=
  roundtrip_step skipMachine c coin

theorem skipProgram_run (c : Config 4 2) (bits : List Bool) :
    skipProgram.toMachine.run c bits = skipMachine.run c bits :=
  roundtrip_run skipMachine c bits

theorem skip_tag_false (xs out tmp ix : List Bool) (coin : Bool) :
    skipMachine.step (config (some (0 : Fin 2)) (false :: xs) out tmp ix) coin =
      config (some (1 : Fin 2)) xs out tmp ix := by
  unfold skipMachine config
  erw [step_compile]
  apply config_ext
  · simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode]
  · intro j
    fin_cases j <;> simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode,
      Instruction.action, StackAction.apply]

theorem skip_tag_true (xs out tmp ix : List Bool) (coin : Bool) :
    skipMachine.step (config (some (0 : Fin 2)) (true :: xs) out tmp ix) coin =
      config none xs out tmp ix := by
  unfold skipMachine config
  erw [step_compile]
  apply config_ext
  · simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode]
    rfl
  · intro j
    fin_cases j <;> simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode,
      Instruction.action, StackAction.apply]

theorem skip_data (bit : Bool) (xs out tmp ix : List Bool) (coin : Bool) :
    skipMachine.step (config (some (1 : Fin 2)) (bit :: xs) out tmp ix) coin =
      config (some (0 : Fin 2)) xs out tmp ix := by
  unfold skipMachine config
  erw [step_compile]
  cases bit <;> apply config_ext
  all_goals
    first | (solve | simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode]) |
      (intro j; fin_cases j <;> simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode,
        Instruction.action, StackAction.apply])

theorem skip_frame (payload tail out tmp ix bits : List Bool)
    (hlen : bits.length = 2 * payload.length + 1) :
    skipMachine.run (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) out tmp ix) bits =
      config none tail out tmp ix ∧
    ActiveFor skipProgram (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) out tmp ix) bits := by
  induction payload generalizing bits with
  | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          have hr : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons, List.length_nil] at hlen
            omega
          subst rest
          constructor
          · simpa [KS.W01.frame, Machine.run] using skip_tag_true tail out tmp ix coin
          · exact ⟨Option.some_ne_none _, trivial⟩
  | cons bit payload ih =>
      cases bits with
      | nil => simp at hlen
      | cons c₀ rest =>
          cases rest with
          | nil => simp at hlen
          | cons c₁ rest =>
              have hr : rest.length = 2 * payload.length + 1 := by
                simp only [List.length_cons] at hlen
                omega
              obtain ⟨he, ha⟩ := ih rest hr
              constructor
              · simp only [KS.W01.frame, List.cons_append, Machine.run]
                erw [skip_tag_false, skip_data]
                exact he
              · erw [ActiveFor.eq_2]
                refine ⟨Option.some_ne_none _, ?_⟩
                erw [skipProgram_step]
                simp only [KS.W01.frame, List.cons_append]
                erw [skip_tag_false]
                erw [ActiveFor.eq_2]
                refine ⟨Option.some_ne_none _, ?_⟩
                erw [skipProgram_step]
                erw [skip_data]
                exact ha

theorem skip_frame_haltsAfter (payload tail out tmp ix bits : List Bool)
    (hlen : bits.length = 2 * payload.length + 1) :
    HaltsAfter skipProgram (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) out tmp ix) bits := by
  have h := skip_frame payload tail out tmp ix bits hlen
  refine ⟨h.2, ?_⟩
  erw [skipProgram_run]
  exact congrArg (fun c : Config 4 2 => c.state) h.1

def indexGuard (heads : Fin 4 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 4 :=
  if (heads 3).val = 0 then ⟨.halt, Vector.replicate 4 .stay⟩
  else ⟨.call, Vector.ofFn (fun j => if j = 3 then .pop else .stay)⟩

def scanProgram : Program 4 := KS.W29.FixedLoop.loop skipProgram indexGuard

theorem scan_guard_nil (input out tmp : List Bool) (coin : Bool) :
    scanProgram.toMachine.step (config (some scanProgram.initial) input out tmp []) coin =
      config none input out tmp [] := by
  change (KS.W29.FixedLoop.loop skipProgram indexGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState skipProgram), «stacks» input out tmp []⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, config]
    rfl
  · intro j
    fin_cases j <;> simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, Instruction.action, StackAction.apply, config]

theorem scan_guard_cons (input out tmp ix : List Bool) (coin : Bool) :
    scanProgram.toMachine.step
      (config (some scanProgram.initial) input out tmp (true :: ix)) coin =
      KS.W29.FixedLoop.liftBody skipProgram (config (some (0 : Fin 2)) input out tmp ix) := by
  change (KS.W29.FixedLoop.loop skipProgram indexGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState skipProgram), «stacks» input out tmp (true :: ix)⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody, config]; rfl
  · intro j
    fin_cases j <;> simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody,
      Instruction.action, StackAction.apply, config]

def scanFuel («prefix» : List (List Bool)) : ℕ :=
  («prefix».flatMap KS.W01.frame).length + «prefix».length + 1

theorem scanFuel_cons (p : List Bool) (ps : List (List Bool)) :
    scanFuel (p :: ps) = 1 + (2 * p.length + 1) + scanFuel ps := by
  simp only [scanFuel, List.flatMap_cons, List.length_append, KS.W01.length_frame,
    List.length_cons]
  omega

theorem scan_prefix («prefix» : List (List Bool)) (tail out tmp bits : List Bool)
    (hlen : bits.length = scanFuel «prefix») :
    scanProgram.toMachine.run
      (config (some scanProgram.initial) («prefix».flatMap KS.W01.frame ++ tail)
        out tmp (List.replicate «prefix».length true)) bits =
      config none tail out tmp [] := by
  induction «prefix» generalizing bits with
  | nil =>
      cases bits with
      | nil => simp [scanFuel] at hlen
      | cons coin rest =>
          have hr : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [scanFuel, List.flatMap_nil, List.length_nil, List.length_cons] at hlen
            omega
          subst rest
          simpa [Machine.run] using scan_guard_nil tail out tmp coin
  | cons p ps ih =>
      cases bits with
      | nil => simp [scanFuel] at hlen
      | cons coin rest =>
          have hr : rest.length = (2 * p.length + 1) + scanFuel ps := by
            rw [scanFuel_cons] at hlen
            simp only [List.length_cons] at hlen
            omega
          have ht : (rest.take (2 * p.length + 1)).length = 2 * p.length + 1 := by
            simp only [List.length_take, hr]
            omega
          have hd : (rest.drop (2 * p.length + 1)).length = scanFuel ps := by
            simp only [List.length_drop, hr]
            omega
          simp only [List.flatMap_cons, List.append_assoc, List.length_cons,
            List.replicate_succ, Machine.run]
          rw [scan_guard_cons]
          conv_lhs => rw [← List.take_append_drop (2 * p.length + 1) rest]
          erw [KS.W29.FixedLoop.run_body_then skipProgram indexGuard _ _ _
            (skip_frame_haltsAfter p (ps.flatMap KS.W01.frame ++ tail) out tmp
              (List.replicate ps.length true) _ ht)]
          erw [skipProgram_run]
          erw [(skip_frame p (ps.flatMap KS.W01.frame ++ tail) out tmp
            (List.replicate ps.length true) _ ht).1]
          exact ih _ hd

end KS.W11.FramedArray

end OAI
