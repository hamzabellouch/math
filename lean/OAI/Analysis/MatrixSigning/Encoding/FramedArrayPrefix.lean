import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.FramedArraySkip

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack
open KS.W29 (StackAction)
open KS.W29.FixedSequential

def «stacks» (src replacement «prefix» scratch index : List Bool) : Fin 5 → List Bool :=
  fun j => if j = 0 then src else if j = 1 then replacement else if j = 2 then «prefix»
    else if j = 3 then scratch else index

def config {q : ℕ} (state : Option (Fin q))
    (src replacement «prefix» scratch index : List Bool) : Config 5 q :=
  ⟨state, «stacks» src replacement «prefix» scratch index⟩

theorem config_ext {q : ℕ} {c d : Config 5 q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

def transferDispatch (s : Fin 2) (heads : Fin 5 → Fin 3) (_coin : Bool) : Instruction 5 2 :=
  if (heads 0).val = 0 then Instruction.halt 5 2 else
    ⟨if s = 0 then (if (heads 0).val = 2 then none else some 1) else some 0,
      Vector.ofFn (fun j => if j = 0 then .pop else if j = 2 then .push ((heads 0).val == 2)
        else .stay)⟩

def transferMachine : Machine := compile 0 0 2 transferDispatch
def transferProgram : Program 5 := ofMachine transferMachine

private theorem roundtrip_step (M : Machine) (c : Config M.stackCount M.states) (coin : Bool) :
    (ofMachine M).toMachine.step c coin = M.step c coin := by
  cases M
  rfl
private theorem roundtrip_run (M : Machine) (c : Config M.stackCount M.states) (bits : List Bool) :
    (ofMachine M).toMachine.run c bits = M.run c bits := by
  cases M
  rfl
theorem transferProgram_step (c : Config 5 2) (coin : Bool) :
    transferProgram.toMachine.step c coin = transferMachine.step c coin := roundtrip_step transferMachine c coin
theorem transferProgram_run (c : Config 5 2) (bits : List Bool) :
    transferProgram.toMachine.run c bits = transferMachine.run c bits := roundtrip_run transferMachine c bits

theorem transfer_tag_false (xs rep pref tmp ix : List Bool) (coin : Bool) :
    transferMachine.step (config (some (0 : Fin 2)) (false :: xs) rep pref tmp ix) coin =
      config (some (1 : Fin 2)) xs rep (false :: pref) tmp ix := by
  unfold transferMachine config
  erw [step_compile]
  apply config_ext
  · simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode]
  · intro j
    fin_cases j <;> simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode,
      Instruction.action, StackAction.apply]

theorem transfer_tag_true (xs rep pref tmp ix : List Bool) (coin : Bool) :
    transferMachine.step (config (some (0 : Fin 2)) (true :: xs) rep pref tmp ix) coin =
      config none xs rep (true :: pref) tmp ix := by
  unfold transferMachine config
  erw [step_compile]
  apply config_ext
  · simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode]
    rfl
  · intro j
    fin_cases j <;> simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode,
      Instruction.action, StackAction.apply]

theorem transfer_data (bit : Bool) (xs rep pref tmp ix : List Bool) (coin : Bool) :
    transferMachine.step (config (some (1 : Fin 2)) (bit :: xs) rep pref tmp ix) coin =
      config (some (0 : Fin 2)) xs rep (bit :: pref) tmp ix := by
  unfold transferMachine config
  erw [step_compile]
  cases bit <;> apply config_ext
  all_goals
    first | (solve | simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode]) |
      (intro j; fin_cases j <;> simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode,
        Instruction.action, StackAction.apply])

private theorem run_two_of_steps (M : Machine) (c d e : Config M.stackCount M.states)
    (b₀ b₁ : Bool) (rest : List Bool) (h₀ : M.step c b₀ = d) (h₁ : M.step d b₁ = e) :
    M.run c (b₀ :: b₁ :: rest) = M.run e rest := by
  rw [Machine.run, h₀, Machine.run, h₁]

theorem transfer_frame (payload tail rep pref tmp ix bits : List Bool)
    (hlen : bits.length = 2 * payload.length + 1) :
    transferMachine.run (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) rep pref tmp ix) bits =
      config none tail rep ((KS.W01.frame payload).reverse ++ pref) tmp ix ∧
    ActiveFor transferProgram
      (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) rep pref tmp ix) bits := by
  induction payload generalizing pref bits with
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
          · simpa [KS.W01.frame, Machine.run] using transfer_tag_true tail rep pref tmp ix coin
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
              obtain ⟨he, ha⟩ := ih (bit :: false :: pref) rest hr
              constructor
              · have hs := run_two_of_steps transferMachine _ _ _ c₀ c₁ rest
                  (transfer_tag_false (bit :: (KS.W01.frame payload ++ tail)) rep pref tmp ix c₀)
                  (transfer_data bit (KS.W01.frame payload ++ tail) rep (false :: pref) tmp ix c₁)
                exact hs.trans (by
                  simp only [KS.W01.frame, List.reverse_cons, List.append_assoc,
                    List.singleton_append] at he ⊢
                  exact he)
              · erw [ActiveFor.eq_2]
                refine ⟨Option.some_ne_none _, ?_⟩
                erw [transferProgram_step]
                simp only [KS.W01.frame, List.cons_append]
                erw [transfer_tag_false]
                erw [ActiveFor.eq_2]
                refine ⟨Option.some_ne_none _, ?_⟩
                erw [transferProgram_step]
                erw [transfer_data]
                exact ha

theorem transfer_frame_haltsAfter (payload tail rep pref tmp ix bits : List Bool)
    (hlen : bits.length = 2 * payload.length + 1) :
    HaltsAfter transferProgram
      (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) rep pref tmp ix) bits := by
  have h := transfer_frame payload tail rep pref tmp ix bits hlen
  refine ⟨h.2, ?_⟩
  erw [transferProgram_run]
  exact congrArg (fun c : Config 5 2 => c.state) h.1

def indexGuard (heads : Fin 5 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 5 :=
  if (heads 4).val = 0 then ⟨.halt, Vector.replicate 5 .stay⟩
  else ⟨.call, Vector.ofFn (fun j => if j = 4 then .pop else .stay)⟩

def prefixProgram : Program 5 := KS.W29.FixedLoop.loop transferProgram indexGuard

theorem prefix_guard_nil (src rep pref tmp : List Bool) (coin : Bool) :
    prefixProgram.toMachine.step (config (some prefixProgram.initial) src rep pref tmp []) coin =
      config none src rep pref tmp [] := by
  change (KS.W29.FixedLoop.loop transferProgram indexGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState transferProgram), «stacks» src rep pref tmp []⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, config]
    rfl
  · intro j
    fin_cases j <;> simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, Instruction.action, StackAction.apply, config]

theorem prefix_guard_cons (src rep pref tmp ix : List Bool) (coin : Bool) :
    prefixProgram.toMachine.step
      (config (some prefixProgram.initial) src rep pref tmp (true :: ix)) coin =
      KS.W29.FixedLoop.liftBody transferProgram (config (some (0 : Fin 2)) src rep pref tmp ix) := by
  change (KS.W29.FixedLoop.loop transferProgram indexGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState transferProgram), «stacks» src rep pref tmp (true :: ix)⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody, config]
    rfl
  · intro j
    fin_cases j <;> simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody,
      Instruction.action, StackAction.apply, config]

theorem transfer_prefix («prefix» : List (List Bool)) (tail rep pref tmp bits : List Bool)
    (hlen : bits.length = KS.W11.FramedArray.scanFuel «prefix») :
    prefixProgram.toMachine.run
      (config (some prefixProgram.initial) («prefix».flatMap KS.W01.frame ++ tail)
        rep pref tmp (List.replicate «prefix».length true)) bits =
      config none tail rep ((«prefix».flatMap KS.W01.frame).reverse ++ pref) tmp [] := by
  induction «prefix» generalizing pref bits with
  | nil =>
      cases bits with
      | nil => simp [KS.W11.FramedArray.scanFuel] at hlen
      | cons coin rest =>
          have hr : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [KS.W11.FramedArray.scanFuel, List.flatMap_nil, List.length_nil,
              List.length_cons] at hlen
            omega
          subst rest
          simpa [Machine.run] using prefix_guard_nil tail rep pref tmp coin
  | cons p ps ih =>
      cases bits with
      | nil => simp [KS.W11.FramedArray.scanFuel] at hlen
      | cons coin rest =>
          have hr : rest.length = (2 * p.length + 1) + KS.W11.FramedArray.scanFuel ps := by
            rw [KS.W11.FramedArray.scanFuel_cons] at hlen
            simp only [List.length_cons] at hlen
            omega
          have ht : (rest.take (2 * p.length + 1)).length = 2 * p.length + 1 := by
            simp only [List.length_take, hr]
            omega
          have hd : (rest.drop (2 * p.length + 1)).length = KS.W11.FramedArray.scanFuel ps := by
            simp only [List.length_drop, hr]
            omega
          simp only [List.flatMap_cons, List.append_assoc, List.length_cons,
            List.replicate_succ, Machine.run]
          rw [prefix_guard_cons]
          conv_lhs => rw [← List.take_append_drop (2 * p.length + 1) rest]
          erw [KS.W29.FixedLoop.run_body_then transferProgram indexGuard _ _ _
            (transfer_frame_haltsAfter p (ps.flatMap KS.W01.frame ++ tail) rep pref tmp
              (List.replicate ps.length true) _ ht)]
          erw [transferProgram_run]
          erw [(transfer_frame p (ps.flatMap KS.W01.frame ++ tail) rep pref tmp
            (List.replicate ps.length true) _ ht).1]
          have hi := ih ((KS.W01.frame p).reverse ++ pref) _ hd
          simp only [List.reverse_append, List.append_assoc] at hi ⊢
          exact hi

end KS.W11.FramedArrayRewrite

end OAI
