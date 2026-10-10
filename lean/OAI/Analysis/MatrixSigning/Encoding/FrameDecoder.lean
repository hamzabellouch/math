import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FiniteDispatch
import OAI.Analysis.MatrixSigning.Encoding.BinaryEncoding

namespace OAI

section

namespace KS.W29
namespace FrameDecoder

def config (s : Option (Fin 3)) (input output scratch : List Bool) : Config 3 :=
  ⟨s, fun j => if j = 0 then input else if j = 1 then output else scratch⟩

def tagEntry (top : Nat) : Instruction 3 :=
  if top = 0 then Instruction.halt 3
  else if top = 1 then ⟨some 1, .pop, .stay, .stay⟩
  else ⟨some 2, .pop, .stay, .stay⟩

def dataEntry (top : Nat) : Instruction 3 :=
  if top = 0 then Instruction.halt 3
  else ⟨some 0, .pop, .stay, .push (top == 2)⟩

def reverseEntry (top : Nat) : Instruction 3 :=
  if top = 0 then Instruction.halt 3
  else ⟨some 2, .stay, .push (top == 2), .pop⟩

def dispatch (s : Fin 3) (heads : Fin 27) (_coin : Bool) : Instruction 3 :=
  if s.val = 0 then tagEntry (heads.val % 3)
  else if s.val = 1 then dataEntry (heads.val % 3)
  else reverseEntry (heads.val / 9)

def machine : BinaryMachine := FiniteDispatch.compile 0 dispatch

theorem first_head (c : Config 3) : headCode c % 3 = topCode (c.«stacks» 0) := by
  have h₀ := topCode_lt_three (c.«stacks» 0)
  unfold headCode
  omega

theorem third_head (c : Config 3) : headCode c / 9 = topCode (c.«stacks» 2) := by
  have h₀ := topCode_lt_three (c.«stacks» 0)
  have h₁ := topCode_lt_three (c.«stacks» 1)
  unfold headCode
  omega

theorem tag_false_step (xs ys zs : List Bool) (b : Bool) :
    machine.step (config (some 0) (false :: xs) ys zs) b =
      config (some 1) xs ys zs := by
  unfold machine config
  erw [FiniteDispatch.step_compile]
  dsimp only
  simp only [dispatch, first_head]
  change Config.mk (some (1 : Fin 3)) _ = Config.mk (some (1 : Fin 3)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem tag_true_step (xs ys zs : List Bool) (b : Bool) :
    machine.step (config (some 0) (true :: xs) ys zs) b =
      config (some 2) xs ys zs := by
  unfold machine config
  erw [FiniteDispatch.step_compile]
  dsimp only
  simp only [dispatch, first_head]
  change Config.mk (some (2 : Fin 3)) _ = Config.mk (some (2 : Fin 3)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem data_step (x : Bool) (xs ys zs : List Bool) (b : Bool) :
    machine.step (config (some 1) (x :: xs) ys zs) b =
      config (some 0) xs ys (x :: zs) := by
  unfold machine config
  erw [FiniteDispatch.step_compile]
  dsimp only
  simp only [dispatch, first_head]
  cases x <;> change Config.mk (some (0 : Fin 3)) _ = Config.mk (some (0 : Fin 3)) _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem reverse_step (x : Bool) (xs ys zs : List Bool) (b : Bool) :
    machine.step (config (some 2) xs ys (x :: zs)) b =
      config (some 2) xs (x :: ys) zs := by
  unfold machine config
  erw [FiniteDispatch.step_compile]
  dsimp only
  simp only [dispatch, third_head]
  cases x <;> change Config.mk (some (2 : Fin 3)) _ = Config.mk (some (2 : Fin 3)) _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem reverse_done (xs ys : List Bool) (b : Bool) :
    machine.step (config (some 2) xs ys []) b = config none xs ys [] := by
  unfold machine config
  erw [FiniteDispatch.step_compile]
  dsimp only
  simp only [dispatch, third_head]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_read (payload tail out scratch bits : List Bool)
    (h : bits.length = 2 * payload.length + 1) :
    machine.run (config (some 0) (W01.frame payload ++ tail) out scratch) bits =
      config (some 2) tail out (payload.reverse ++ scratch) := by
  induction payload generalizing scratch bits with
  | nil =>
      cases bits with
      | nil => simp at h
      | cons b bs =>
          have hb : bs = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons, List.length_nil] at h
            omega
          subst bs
          simpa [W01.frame, BinaryMachine.run] using tag_true_step tail out scratch b
  | cons x xs ih =>
      cases bits with
      | nil => simp at h
      | cons b₀ bs =>
          cases bs with
          | nil => simp at h
          | cons b₁ rest =>
              have hr : rest.length = 2 * xs.length + 1 := by
                simp only [List.length_cons] at h
                omega
              simp only [W01.frame, List.cons_append, BinaryMachine.run]
              rw [tag_false_step, data_step, ih _ _ hr]
              simp [List.reverse_cons, List.append_assoc]
              rfl

theorem run_reverse (input output scratch bits : List Bool)
    (h : bits.length = scratch.length + 1) :
    machine.run (config (some 2) input output scratch) bits =
      config none input (scratch.reverse ++ output) [] := by
  induction scratch generalizing output bits with
  | nil =>
      cases bits with
      | nil => simp at h
      | cons b bs =>
          have hb : bs = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons, List.length_nil] at h
            omega
          subst bs
          simpa [BinaryMachine.run] using reverse_done input output b
  | cons x xs ih =>
      cases bits with
      | nil => simp at h
      | cons b bs =>
          have hb : bs.length = xs.length + 1 := by simpa using h
          erw [BinaryMachine.run, reverse_step, ih _ _ hb]
          simp [List.reverse_cons, List.append_assoc]
          rfl

theorem run_frame (payload tail bits : List Bool)
    (h : bits.length = 3 * payload.length + 2) :
    machine.run (machine.init (W01.frame payload ++ tail)) bits =
      config none tail payload [] := by
  have hi : machine.init (W01.frame payload ++ tail) =
      config (some 0) (W01.frame payload ++ tail) [] [] := by
    simp [BinaryMachine.init, machine, FiniteDispatch.compile, config]
  rw [hi]
  have hl : (bits.take (2 * payload.length + 1)).length = 2 * payload.length + 1 := by
    simp only [List.length_take, h]
    omega
  have hr : (bits.drop (2 * payload.length + 1)).length = payload.length + 1 := by
    simp only [List.length_drop, h]
    omega
  conv_lhs => rw [← List.take_append_drop (2 * payload.length + 1) bits]
  erw [machine.run_append, run_read _ _ _ _ _ hl]
  simp only [List.append_nil]
  rw [run_reverse]
  · simp
    rfl
  · simpa using hr

theorem haltsWithin (payload tail : List Bool) :
    machine.HaltsWithin (W01.frame payload ++ tail) (3 * payload.length + 2) := by
  rw [machine.haltsWithin_iff_bitLists]
  intro bits hb
  rw [run_frame payload tail bits hb]
  rfl

theorem output_eq (payload tail bits : List Bool) (h : bits.length = 3 * payload.length + 2) :
    machine.output (W01.frame payload ++ tail) bits = payload := by
  unfold BinaryMachine.output
  rw [run_frame payload tail bits h]
  rfl

theorem preserved_suffix (payload tail bits : List Bool)
    (h : bits.length = 3 * payload.length + 2) :
    (machine.run (machine.init (W01.frame payload ++ tail)) bits).«stacks» 0 = tail := by
  rw [run_frame payload tail bits h]
  rfl

theorem run_frame_of_length_ge (payload tail bits : List Bool)
    (h : 3 * payload.length + 2 ≤ bits.length) :
    machine.run (machine.init (W01.frame payload ++ tail)) bits =
      config none tail payload [] := by
  have htake : (bits.take (3 * payload.length + 2)).length = 3 * payload.length + 2 := by
    simp [List.length_take, Nat.min_eq_left h]
  have hr := run_frame payload tail (bits.take (3 * payload.length + 2)) htake
  conv_lhs => rw [← List.take_append_drop (3 * payload.length + 2) bits]
  erw [machine.run_append, hr]
  exact machine.run_halted _ rfl _

theorem haltsWithin_polynomialFuel (payload tail : List Bool) :
    machine.HaltsWithin (W01.frame payload ++ tail)
      (polynomialFuel 2 1 (W01.frame payload ++ tail).length) := by
  apply machine.haltsWithin_mono _ (haltsWithin payload tail)
  simp only [polynomialFuel, pow_one, List.length_append, W01.length_frame]
  omega

end FrameDecoder
end KS.W29

end

end OAI
