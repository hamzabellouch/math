import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FiniteDispatch
import OAI.Analysis.MatrixSigning.Encoding.BinaryEncoding

namespace OAI

section

namespace KS.W28.PositiveWireSerializer
open KS.W29

def dispatch (s : Fin 5) (heads : Fin 27) (_coin : Bool) : Instruction 5 :=
  if s = 4 then ⟨some 0, .stay, .stay, .push false⟩
  else if s = 0 then
    if heads.val % 3 = 0 then ⟨some 2, .stay, .stay, .push true⟩
    else ⟨some 1, .stay, .stay, .push false⟩
  else if s = 1 then ⟨some 0, .pop, .stay, .push (heads.val % 3 == 2)⟩
  else if s = 2 then
    if heads.val / 3 % 3 = 0 then ⟨none, .stay, .stay, .push true⟩
    else ⟨some 3, .stay, .stay, .push false⟩
  else ⟨some 2, .stay, .pop, .push (heads.val / 3 % 3 == 2)⟩

def machine : BinaryMachine := FiniteDispatch.compile 4 dispatch

def cfg (state : Option (Fin 5)) (xs ys zs : List Bool) : Config 5 :=
  ⟨state, fun j => if j = 0 then xs else if j = 1 then ys else zs⟩

def wire (xs ys : List Bool) : List Bool := false :: (KS.W01.frame xs ++ KS.W01.frame ys)

theorem table_length : machine.table.length = 270 := by
  simp only [machine, FiniteDispatch.compile, List.length_ofFn]

theorem head_left (c : Config 5) : headCode c % 3 = topCode (c.«stacks» 0) := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  unfold headCode
  omega

theorem head_right (c : Config 5) : headCode c / 3 % 3 = topCode (c.«stacks» 1) := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  have h1 := topCode_lt_three (c.«stacks» 1)
  unfold headCode
  omega

theorem step_start (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 4) xs ys zs) coin = cfg (some 0) xs ys (false :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_num_prefix (a : Bool) (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 0) (a :: xs) ys zs) coin =
      cfg (some 1) (a :: xs) ys (false :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left]
  cases a <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_num_digit (a : Bool) (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 1) (a :: xs) ys zs) coin =
      cfg (some 0) xs ys (a :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left]
  cases a <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_num_done (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 0) [] ys zs) coin = cfg (some 2) [] ys (true :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_den_prefix (b : Bool) (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 2) [] (b :: ys) zs) coin =
      cfg (some 3) [] (b :: ys) (false :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left, head_right]
  cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_den_digit (b : Bool) (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 3) [] (b :: ys) zs) coin = cfg (some 2) [] ys (b :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left, head_right]
  cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_den_done (zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 2) [] [] zs) coin = cfg none [] [] (true :: zs) := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  simp only [dispatch, head_left, head_right]
  change Config.mk _ _ = Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_den (ys zs coins : List Bool) (hlen : coins.length = 2 * ys.length + 1) :
    machine.run (cfg (some 2) [] ys zs) coins =
      cfg none [] [] ((KS.W01.frame ys).reverse ++ zs) := by
  induction ys generalizing zs coins with
  | nil =>
      cases coins with
      | nil => simp at hlen
      | cons c cs =>
          have hc : cs = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons, List.length_nil] at hlen
            omega
          subst cs
          erw [BinaryMachine.run, step_den_done]
          rfl
  | cons b ys ih =>
      cases coins with
      | nil => simp at hlen
      | cons c cs =>
          cases cs with
          | nil => simp at hlen
          | cons d ds =>
              have hd : ds.length = 2 * ys.length + 1 := by
                simp only [List.length_cons] at hlen
                omega
              erw [BinaryMachine.run, step_den_prefix, BinaryMachine.run, step_den_digit, ih _ _ hd]
              simp [KS.W01.frame, List.reverse_cons, List.append_assoc]
              rfl

theorem run_num (xs ys zs coins : List Bool)
    (hlen : coins.length = 2 * xs.length + 2 * ys.length + 2) :
    machine.run (cfg (some 0) xs ys zs) coins =
      cfg none [] [] ((KS.W01.frame xs ++ KS.W01.frame ys).reverse ++ zs) := by
  induction xs generalizing zs coins with
  | nil =>
      cases coins with
      | nil => simp at hlen
      | cons c cs =>
          have hc : cs.length = 2 * ys.length + 1 := by
            simp only [List.length_cons, List.length_nil] at hlen
            omega
          erw [BinaryMachine.run, step_num_done, run_den _ _ _ hc]
          simp [KS.W01.frame, List.reverse_cons, List.append_assoc]
          rfl
  | cons a xs ih =>
      cases coins with
      | nil => simp at hlen
      | cons c cs =>
          cases cs with
          | nil => simp at hlen
          | cons d ds =>
              have hd : ds.length = 2 * xs.length + 2 * ys.length + 2 := by
                simp only [List.length_cons] at hlen
                omega
              erw [BinaryMachine.run, step_num_prefix, BinaryMachine.run, step_num_digit, ih _ _ hd]
              simp [KS.W01.frame, List.reverse_cons, List.reverse_append, List.append_assoc]
              rfl

theorem run_wire (xs ys zs coins : List Bool)
    (hlen : coins.length = 2 * xs.length + 2 * ys.length + 3) :
    machine.run (cfg (some 4) xs ys zs) coins =
      cfg none [] [] ((wire xs ys).reverse ++ zs) := by
  cases coins with
  | nil => simp at hlen
  | cons c cs =>
      have hc : cs.length = 2 * xs.length + 2 * ys.length + 2 := by
        simp only [List.length_cons] at hlen
        omega
      erw [BinaryMachine.run, step_start, run_num _ _ _ _ hc]
      simp [wire, List.reverse_cons, List.append_assoc]
      rfl

theorem wire_length (xs ys : List Bool) :
    (wire xs ys).length = 2 * xs.length + 2 * ys.length + 3 := by
  simp [wire, KS.W01.length_frame]
  omega

end KS.W28.PositiveWireSerializer

end

end OAI
