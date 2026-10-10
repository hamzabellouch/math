import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedStackMachine

namespace OAI

section

namespace KS.W03.BinaryToUnary
open KS.W01.FixedStack KS.W29

def doubleState (b : Bool) : Fin 8 := if b then 5 else 2
def secondState (b : Bool) : Fin 8 := if b then 6 else 3
def restoreState (b : Bool) : Fin 8 := if b then 7 else 4

def instruction (next : Option (Fin 8)) (a b c : StackAction) :
    KS.W01.FixedStack.Instruction 3 8 :=
  ⟨next, Vector.ofFn ![a, b, c]⟩

def dispatch (s : Fin 8) (heads : Fin 3 → Fin 3) (_coin : Bool) :
    KS.W01.FixedStack.Instruction 3 8 :=
  if s = 0 then
    if heads 0 = 0 then instruction (some 1) .stay .stay .stay
    else instruction (some 0) .pop .stay (.push (heads 0 == 2))
  else if s = 1 then
    if heads 2 = 0 then instruction none .stay .stay .stay
    else instruction (some (doubleState (heads 2 == 2))) .stay .stay .pop
  else if s = 2 ∨ s = 5 then
    let b := s == 5
    if heads 1 = 0 then instruction (some (restoreState b)) .stay .stay .stay
    else instruction (some (secondState b)) (.push true) .pop .stay
  else if s = 3 ∨ s = 6 then
    instruction (some (doubleState (s == 6))) (.push true) .stay .stay
  else
    let b := s == 7
    if heads 0 = 0 then
      instruction (some 1) .stay (if b then .push true else .stay) .stay
    else instruction (some (restoreState b)) .pop (.push true) .stay

def machine : Machine := compile (0 : Fin 8) (0 : Fin 3) (1 : Fin 3) dispatch

def cfg (s : Option (Fin 8)) (scratch counter unread : List Bool) :
    KS.W01.FixedStack.Config 3 8 := ⟨s, ![scratch, counter, unread]⟩

theorem init_eq (xs : List Bool) : machine.init xs = cfg (some 0) xs [] [] := by
  change KS.W01.FixedStack.Config.mk (some (0 : Fin 8)) _ =
    KS.W01.FixedStack.Config.mk (some (0 : Fin 8)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem reverse_step (b coin : Bool) (xs ys zs : List Bool) :
    machine.step (cfg (some 0) (b :: xs) ys zs) coin =
      cfg (some 0) xs ys (b :: zs) := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem reverse_done (coin : Bool) (ys zs : List Bool) :
    machine.step (cfg (some 0) [] ys zs) coin = cfg (some 1) [] ys zs := by
  unfold machine
  erw [step_compile]
  change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem guard_done (coin : Bool) (counter : List Bool) :
    machine.step (cfg (some 1) [] counter []) coin = cfg none [] counter [] := by
  unfold machine
  erw [step_compile]
  change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem guard_step (b coin : Bool) (counter unread : List Bool) :
    machine.step (cfg (some 1) [] counter (b :: unread)) coin =
      cfg (some (doubleState b)) [] counter unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem double_step (b coin : Bool) (scratch counter unread : List Bool) :
    machine.step (cfg (some (doubleState b)) scratch (true :: counter) unread) coin =
      cfg (some (secondState b)) (true :: scratch) counter unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem second_step (b coin : Bool) (scratch counter unread : List Bool) :
    machine.step (cfg (some (secondState b)) scratch counter unread) coin =
      cfg (some (doubleState b)) (true :: scratch) counter unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem double_done (b coin : Bool) (scratch unread : List Bool) :
    machine.step (cfg (some (doubleState b)) scratch [] unread) coin =
      cfg (some (restoreState b)) scratch [] unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem restore_step (b coin : Bool) (scratch counter unread : List Bool) :
    machine.step (cfg (some (restoreState b)) (true :: scratch) counter unread) coin =
      cfg (some (restoreState b)) scratch (true :: counter) unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem restore_done (b coin : Bool) (counter unread : List Bool) :
    machine.step (cfg (some (restoreState b)) [] counter unread) coin =
      cfg (some 1) [] (if b then true :: counter else counter) unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

end KS.W03.BinaryToUnary

end

end OAI
