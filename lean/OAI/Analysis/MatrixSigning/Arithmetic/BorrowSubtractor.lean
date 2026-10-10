import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FiniteDispatch
import OAI.Analysis.MatrixSigning.Arithmetic.SubtractionBorrow

namespace OAI

namespace KS.W19.BorrowSubtractor
open KS.W29
open KS.W19 (bitsValue digit differenceDigit nextBorrow subtractBits)

def borrowState (c : Bool) : Fin 2 := if c then 1 else 0

def finishEntry (c : Bool) : Instruction 2 :=
  ⟨none, .push c, .stay, .stay⟩

def subEntry (c a b : Bool) : Instruction 2 :=
  ⟨some (borrowState (nextBorrow a b c)), .pop, .pop, .push (differenceDigit a b c)⟩

def dispatch (s : Fin 2) (heads : Fin 27) (_coin : Bool) : Instruction 2 :=
  let c := s.val == 1
  let left := heads.val % 3
  let right := heads.val / 3 % 3
  if left = 0 ∧ right = 0 then finishEntry c
  else subEntry c (left == 2) (right == 2)

def machine : BinaryMachine := FiniteDispatch.compile 0 dispatch

def cfg (state : Option (Fin 2)) (xs ys zs : List Bool) : Config 2 :=
  ⟨state, fun j => if j = 0 then xs else if j = 1 then ys else zs⟩

theorem table_lookup (s : Fin 2) (c : Config 2) (coin : Bool) :
    machine.table.getD (transitionIndex s c coin) (Instruction.halt 2) =
      if topCode (c.«stacks» 0) = 0 ∧ topCode (c.«stacks» 1) = 0 then
        finishEntry (s.val == 1)
      else subEntry (s.val == 1) (topCode (c.«stacks» 0) == 2)
        (topCode (c.«stacks» 1) == 2) := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  have h1 := topCode_lt_three (c.«stacks» 1)
  have h2 := topCode_lt_three (c.«stacks» 2)
  have hl : headCode c % 3 = topCode (c.«stacks» 0) := by unfold headCode; omega
  have hr : headCode c / 3 % 3 = topCode (c.«stacks» 1) := by unfold headCode; omega
  unfold machine
  rw [FiniteDispatch.lookup_compile]
  simp only [dispatch, hl, hr]
  rfl

theorem step_left_cons (c a : Bool) (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (borrowState c)) (a :: xs) ys zs) coin =
      cfg (some (borrowState (nextBorrow a (ys.headD false) c))) xs ys.tail
        (differenceDigit a (ys.headD false) c :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> cases a <;> cases ys with
  | nil =>
      change Config.mk _ _ = Config.mk _ _
      congr 1
      funext j
      fin_cases j <;> rfl
  | cons b ys =>
      cases b <;> change Config.mk _ _ = Config.mk _ _
      all_goals
        congr 1
        funext j
        fin_cases j <;> rfl

theorem step_right_cons (c b : Bool) (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (borrowState c)) [] (b :: ys) zs) coin =
      cfg (some (borrowState (nextBorrow false b c))) [] ys
        (differenceDigit false b c :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_done (c : Bool) (zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (borrowState c)) [] [] zs) coin =
      cfg none [c] [] zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases c <;> change Config.mk none _ = Config.mk none _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem run_sub (c : Bool) (xs ys zs bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    machine.run (cfg (some (borrowState c)) xs ys zs) bits =
      cfg none [subtractionBorrow xs ys c] [] ((subtractBits xs ys c).reverse ++ zs) := by
  induction xs generalizing c ys zs bits with
  | nil =>
      induction ys generalizing c zs bits with
      | nil =>
          cases bits with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest = [] := by
                apply List.length_eq_zero_iff.mp
                simp only [List.length_cons, List.length_nil, max_self] at hlen
                omega
              subst rest
              erw [BinaryMachine.run.eq_2, step_done]
              cases c <;> simp [BinaryMachine.run, subtractBits, subtractionBorrow] <;> rfl
      | cons b ys ih =>
          cases bits with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest.length = max ([] : List Bool).length ys.length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.zero_max] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_right_cons, ih _ _ _ hr]
              simp [subtractBits, subtractionBorrow, List.reverse_cons, List.append_assoc]
              rfl
  | cons a xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          cases ys with
          | nil =>
              have hr : rest.length = max xs.length ([] : List Bool).length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.max_zero] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_left_cons]
              simp only [List.headD_nil, List.tail_nil]
              erw [ih _ _ _ _ hr]
              simp [subtractBits, subtractionBorrow, List.reverse_cons, List.append_assoc]
              rfl
          | cons b ys =>
              have hr : rest.length = max xs.length ys.length + 1 := by
                simp only [List.length_cons] at hlen
                omega
              erw [BinaryMachine.run.eq_2, step_left_cons]
              simp only [List.headD_cons, List.tail_cons]
              erw [ih _ _ _ _ hr]
              simp [subtractBits, subtractionBorrow, List.reverse_cons, List.append_assoc]
              rfl

theorem run_borrow_flag (xs ys bits : List Bool)
    (hlen : bits.length = max xs.length ys.length + 1) :
    (machine.run (cfg (some 0) xs ys []) bits).«stacks» 0 =
      [decide (bitsValue xs < bitsValue ys)] := by
  have hr := run_sub false xs ys [] bits hlen
  change machine.run (cfg (some 0) xs ys []) bits = _ at hr
  rw [hr]
  change [subtractionBorrow xs ys false] = [decide (bitsValue xs < bitsValue ys)]
  congr 1
  have hi := subtractionBorrow_true_iff xs ys false
  simp only [digit_false, Nat.add_zero] at hi
  cases hb : subtractionBorrow xs ys false <;> simp_all

theorem table_length : machine.table.length = 108 := by
  simp only [machine, FiniteDispatch.compile, List.length_ofFn]

end KS.W19.BorrowSubtractor

end OAI
