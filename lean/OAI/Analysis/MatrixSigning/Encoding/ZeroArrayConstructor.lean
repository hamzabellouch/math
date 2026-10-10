import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Machines.BinaryStackMoves
import OAI.Analysis.MatrixSigning.Encoding.BinaryEncoding

namespace OAI

namespace KS.W11.ZeroArrayConstructor
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def «stacks» (count accum output : List Bool) : Fin 3 → List Bool :=
  fun j => if j = 0 then count else if j = 1 then accum else output

private theorem config_ext {q : ℕ} {c d : Config 3 q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

def emitDispatch (word : List Bool) (s : Fin (word.length + 1))
    (_heads : Fin 3 → Fin 3) (_coin : Bool) : Instruction 3 (word.length + 1) :=
  if h : s.val < word.length then
    ⟨some ⟨s.val + 1, by omega⟩,
      Vector.ofFn (fun j => if j = 1 then .push word[s.val] else .stay)⟩
  else Instruction.halt 3 (word.length + 1)

def emitProgram (word : List Bool) : Program 3 :=
  ofMachine (compile ⟨0, by omega⟩ 0 1 (emitDispatch word))

theorem emit_step (word : List Bool) (p : ℕ) (hp : p < word.length)
    (count accum output : List Bool) (coin : Bool) :
    (emitProgram word).toMachine.step
      ⟨some ⟨p, by change p < word.length+1;omega⟩, «stacks» count accum output⟩ coin =
      ⟨some ⟨p + 1, by change p+1 < word.length+1;omega⟩, «stacks» count (word[p] :: accum) output⟩ := by
  change (compile _ _ _ (emitDispatch word)).step _ coin = _
  erw [step_compile]
  apply config_ext
  · simp [emitDispatch, hp]
    rfl
  · intro j
    fin_cases j <;> simp [emitDispatch, hp, «stacks», Instruction.action, KS.W29.StackAction.apply]

theorem emit_done (word : List Bool) (count accum output : List Bool) (coin : Bool) :
    (emitProgram word).toMachine.step
      ⟨some ⟨word.length, by change word.length < word.length+1;omega⟩, «stacks» count accum output⟩ coin =
      ⟨none, «stacks» count accum output⟩ := by
  change (compile _ _ _ (emitDispatch word)).step _ coin = _
  erw [step_compile]
  apply config_ext
  · simp [emitDispatch, Instruction.halt]
    rfl
  · intro j
    simp [emitDispatch, Instruction.halt, Instruction.action, KS.W29.StackAction.apply]

theorem run_emit_aux (word : List Bool) (remaining p : ℕ) (hp : p + remaining = word.length)
    (count accum output bits : List Bool) (hlen : bits.length = remaining + 1) :
    (emitProgram word).toMachine.run
      ⟨some ⟨p, by change p < word.length+1;omega⟩, «stacks» count accum output⟩ bits =
      ⟨none, «stacks» count ((word.drop p).reverse ++ accum) output⟩ := by
  induction remaining generalizing p accum bits with
  | zero =>
      have hpe : p = word.length := by omega
      subst p
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          have hr : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons] at hlen
            omega
          subst rest
          simpa [Machine.run] using emit_done word count accum output coin
  | succ remaining ih =>
      have hpl : p < word.length := by omega
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          have hr : rest.length = remaining + 1 := by simpa using hlen
          rw [Machine.run, emit_step word p hpl]
          have h := ih (p + 1) (by omega) (word[p] :: accum) rest hr
          rw [List.drop_eq_getElem_cons hpl]
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h

theorem emit_spec (word count accum output : List Bool) :
    RunSpec (emitProgram word) («stacks» count accum output)
      («stacks» count (word.reverse ++ accum) output) (word.length + 1) := by
  intro bits hbits
  have h := run_emit_aux word word.length 0 (by omega) count accum output bits hbits
  simp only [List.drop_zero] at h
  exact h

def zeroFrame : List Bool := KS.W01.frame (KS.W01.encodeRat 0)
theorem zeroFrame_length : zeroFrame.length = 11 := by decide
def zeroTape (n : ℕ) : List Bool := (List.replicate n zeroFrame).flatten
def bodyProgram : Program 3 := emitProgram zeroFrame

theorem zeroTape_succ (n : ℕ) : zeroTape (n + 1) = zeroFrame ++ zeroTape n := by
  simp [zeroTape, List.replicate_succ]

theorem zeroTape_length (n : ℕ) : (zeroTape n).length = n * zeroFrame.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [zeroTape_succ, List.length_append, ih]
      simp [Nat.succ_mul, Nat.add_comm]

def guard (heads : Fin 3 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 3 :=
  if (heads 0).val = 0 then ⟨.halt, Vector.replicate 3 .stay⟩
  else ⟨.call, Vector.ofFn (fun j => if j = 0 then .pop else .stay)⟩

def loopProgram : Program 3 := KS.W29.FixedLoop.loop bodyProgram guard
def finishProgram : Program 3 := KS.W04.BinaryStackMoves.moveProgram 1 2
def program : Program 3 := compose loopProgram finishProgram

theorem program_states : program.states = zeroFrame.length + 3 := rfl
theorem program_states_numeric : program.states = 14 := by rw [program_states, zeroFrame_length]
theorem program_input : program.input = 0 := rfl
theorem program_output : program.output = 2 := rfl

theorem guard_nil (accum : List Bool) (coin : Bool) :
    loopProgram.toMachine.step ⟨some loopProgram.initial, «stacks» [] accum []⟩ coin =
      ⟨none, «stacks» [] accum []⟩ := by
  change (KS.W29.FixedLoop.loop bodyProgram guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState bodyProgram), _⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · simp [guard, observedHeads, «stacks», KS.W29.topCode, KS.W29.FixedLoop.guardInstruction]
    rfl
  · intro j
    fin_cases j <;> simp [guard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, Instruction.action, KS.W29.StackAction.apply]

theorem guard_cons (count accum : List Bool) (mark coin : Bool) :
    loopProgram.toMachine.step ⟨some loopProgram.initial, «stacks» (mark :: count) accum []⟩ coin =
      KS.W29.FixedLoop.liftBody bodyProgram ⟨some bodyProgram.initial, «stacks» count accum []⟩ := by
  change (KS.W29.FixedLoop.loop bodyProgram guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState bodyProgram), _⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases mark <;> apply config_ext
  all_goals
    first | (solve | simp [guard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody]) |
      (intro j; fin_cases j <;> simp [guard, observedHeads, «stacks», KS.W29.topCode,
        KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody,
        Instruction.action, KS.W29.StackAction.apply])

theorem run_loop (count accum bits : List Bool)
    (hlen : count.length * (zeroFrame.length + 2) + 1 ≤ bits.length) :
    loopProgram.toMachine.run ⟨some loopProgram.initial, «stacks» count accum []⟩ bits =
      ⟨none, «stacks» [] ((zeroTape count.length).reverse ++ accum) []⟩ := by
  induction count generalizing accum bits with
  | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          rw [Machine.run, guard_nil, Machine.run_halted _ _ rfl]
          rfl
  | cons mark count ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          have hb : zeroFrame.length + 1 ≤ rest.length := by
            simp only [List.length_cons, Nat.add_mul] at hlen
            omega
          obtain ⟨remaining, hremaining, he⟩ :=
            (emit_spec zeroFrame count accum []).loop_body_then guard rest hb
          have ht : count.length * (zeroFrame.length + 2) + 1 ≤ remaining.length := by
            simp only [List.length_cons, Nat.add_mul] at hlen
            omega
          rw [Machine.run, guard_cons]
          erw [he]
          have h := ih (zeroFrame.reverse ++ accum) remaining ht
          simp only [List.length_cons, zeroTape_succ, List.reverse_append, List.append_assoc] at h ⊢
          exact h

theorem finish_spec (word : List Bool) :
    RunSpec finishProgram («stacks» [] word.reverse []) («stacks» [] [] word) (word.length + 1) := by
  intro bits hbits
  have h := KS.W04.BinaryStackMoves.run_move_stacks (1 : Fin 3) 2 (by decide)
    («stacks» [] word.reverse []) bits (by simpa [«stacks»] using hbits)
  change (KS.W04.BinaryStackMoves.moveMachine (1 : Fin 3) 2).run
    ⟨some (0 : Fin 1), «stacks» [] word.reverse []⟩ bits = _
  rw [h]
  apply congrArg (Config.mk none)
  funext j
  fin_cases j <;> simp [«stacks»]

theorem zero_spec (count : List Bool) :
    RunSpec program («stacks» count [] []) («stacks» [] [] (zeroTape count.length))
      ((2 * zeroFrame.length + 2) * count.length + 2) := by
  have hl : RunSpec loopProgram («stacks» count [] [])
      («stacks» [] (zeroTape count.length).reverse [])
      (count.length * (zeroFrame.length + 2) + 1) := by
    intro bits hbits
    simpa only [List.append_nil] using run_loop count [] bits hbits.ge
  have h := hl.compose (finish_spec (zeroTape count.length))
  have ht : (count.length * (zeroFrame.length + 2) + 1) + ((zeroTape count.length).length + 1) =
      (2 * zeroFrame.length + 2) * count.length + 2 := by
    rw [zeroTape_length]
    ring
  rw [ht] at h
  exact h

theorem zero_spec_linear (count : List Bool) :
    RunSpec program («stacks» count [] []) («stacks» [] [] (zeroTape count.length))
      (24 * count.length + 2) := by
  simpa only [zeroFrame_length] using zero_spec count

end KS.W11.ZeroArrayConstructor

end OAI
