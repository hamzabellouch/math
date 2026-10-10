import Mathlib
import OAI.Analysis.MatrixSigning.Machines.Sequential
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryDivision

namespace OAI

namespace KS.W28.LittleEndianCompare
open KS.W29
open KS.W19 (bitsValue compareBits compareDigit OrderingCorrect)

def encode : Ordering → Fin 3
  | .eq => 0
  | .lt => 1
  | .gt => 2

def decode (s : Fin 3) : Ordering :=
  if s = 0 then .eq else if s = 1 then .lt else .gt

@[simp] theorem decode_encode (o : Ordering) : decode (encode o) = o := by
  cases o <;> rfl

def merge (old high : Ordering) : Ordering :=
  match high with
  | .eq => old
  | o => o

def update (o : Ordering) (a b : Bool) : Ordering := merge o (compareDigit a b)
def result (o : Ordering) : Bool := match o with | .gt => false | _ => true

def dispatch (s : Fin 3) (heads : Fin 27) (_coin : Bool) : Instruction 3 :=
  let l := heads.val % 3
  let r := heads.val / 3 % 3
  if l = 0 ∧ r = 0 then ⟨none, .stay, .stay, .push (result (decode s))⟩
  else ⟨some (encode (update (decode s) (l == 2) (r == 2))), .pop, .pop, .stay⟩

def machine : BinaryMachine := FiniteDispatch.compile (encode .eq) dispatch

def cfg (state : Option (Fin 3)) (xs ys zs : List Bool) : Config 3 :=
  ⟨state, fun j => if j = 0 then xs else if j = 1 then ys else zs⟩

theorem table_length : machine.table.length = 162 := by
  simp only [machine, FiniteDispatch.compile, List.length_ofFn]

theorem table_lookup (s : Fin 3) (c : Config 3) (coin : Bool) :
    machine.table.getD (transitionIndex s c coin) (Instruction.halt 3) =
      if topCode (c.«stacks» 0) = 0 ∧ topCode (c.«stacks» 1) = 0 then
        ⟨none, .stay, .stay, .push (result (decode s))⟩
      else ⟨some (encode (update (decode s) (topCode (c.«stacks» 0) == 2)
        (topCode (c.«stacks» 1) == 2))), .pop, .pop, .stay⟩ := by
  have h0 := topCode_lt_three (c.«stacks» 0)
  have h1 := topCode_lt_three (c.«stacks» 1)
  have h2 := topCode_lt_three (c.«stacks» 2)
  have hl : headCode c % 3 = topCode (c.«stacks» 0) := by unfold headCode; omega
  have hr : headCode c / 3 % 3 = topCode (c.«stacks» 1) := by unfold headCode; omega
  unfold machine
  rw [FiniteDispatch.lookup_compile]
  simp only [dispatch, hl, hr]
  rfl

theorem step_left (o : Ordering) (a : Bool) (xs ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (encode o)) (a :: xs) ys zs) coin =
      cfg (some (encode (update o a (ys.headD false)))) xs ys.tail zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases o <;> cases a <;> cases ys with
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

theorem step_right (o : Ordering) (b : Bool) (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (encode o)) [] (b :: ys) zs) coin =
      cfg (some (encode (update o false b))) [] ys zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases o <;> cases b <;> change Config.mk _ _ = Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_done (o : Ordering) (zs : List Bool) (coin : Bool) :
    machine.step (cfg (some (encode o)) [] [] zs) coin =
      cfg none [] [] (result o :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases o <;> change Config.mk none _ = Config.mk none _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

def scan (o : Ordering) : List Bool → List Bool → Ordering
  | [], [] => o
  | [], b :: ys => scan (update o false b) [] ys
  | a :: xs, [] => scan (update o a false) xs []
  | a :: xs, b :: ys => scan (update o a b) xs ys
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

theorem scan_eq (o : Ordering) (xs ys : List Bool) :
    scan o xs ys = merge o (compareBits xs ys) := by
  induction xs generalizing o ys with
  | nil =>
      induction ys generalizing o with
      | nil => simp [scan, compareBits, merge]
      | cons b ys ih =>
          rw [scan, ih]
          cases h : compareBits [] ys <;> cases o <;> cases b <;>
            simp [compareBits, h, update, merge, compareDigit]
  | cons a xs ih =>
      cases ys with
      | nil =>
          rw [scan, ih]
          cases h : compareBits xs [] <;> cases o <;> cases a <;>
            simp [compareBits, h, update, merge, compareDigit]
      | cons b ys =>
          rw [scan, ih]
          cases h : compareBits xs ys <;> cases o <;> cases a <;> cases b <;>
            simp [compareBits, h, update, merge, compareDigit]

theorem run_scan (o : Ordering) (xs ys zs coins : List Bool)
    (hlen : coins.length = max xs.length ys.length + 1) :
    machine.run (cfg (some (encode o)) xs ys zs) coins =
      cfg none [] [] (result (scan o xs ys) :: zs) := by
  induction xs generalizing o ys zs coins with
  | nil =>
      induction ys generalizing o zs coins with
      | nil =>
          cases coins with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest = [] := by
                apply List.length_eq_zero_iff.mp
                simp only [List.length_cons, List.length_nil, max_self] at hlen
                omega
              subst rest
              erw [BinaryMachine.run.eq_2, step_done]
              simp only [BinaryMachine.run, scan]
              rfl
      | cons b ys ih =>
          cases coins with
          | nil => simp at hlen
          | cons coin rest =>
              have hr : rest.length = max ([] : List Bool).length ys.length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.zero_max] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_right, ih _ _ _ hr]
              simp only [scan]
              rfl
  | cons a xs ih =>
      cases coins with
      | nil => simp at hlen
      | cons coin rest =>
          cases ys with
          | nil =>
              have hr : rest.length = max xs.length ([] : List Bool).length + 1 := by
                simp only [List.length_nil, List.length_cons, Nat.max_zero] at hlen ⊢
                omega
              erw [BinaryMachine.run.eq_2, step_left]
              simp only [List.headD_nil, List.tail_nil]
              rw [ih _ _ _ _ hr]
              simp only [scan]
              rfl
          | cons b ys =>
              have hr : rest.length = max xs.length ys.length + 1 := by
                simp only [List.length_cons] at hlen
                omega
              erw [BinaryMachine.run.eq_2, step_left]
              simp only [List.headD_cons, List.tail_cons]
              rw [ih _ _ _ _ hr]
              simp only [scan]
              rfl

theorem result_correct (xs ys : List Bool) :
    result (scan .eq xs ys) = decide (bitsValue xs ≤ bitsValue ys) := by
  rw [scan_eq]
  have hc := KS.W19.compareBits_correct xs ys
  cases h : compareBits xs ys with
  | lt =>
      simp only [h, OrderingCorrect] at hc
      simp [merge, result, Nat.le_of_lt hc]
  | eq =>
      simp only [h, OrderingCorrect] at hc
      simp [merge, result, hc]
  | gt =>
      simp only [h, OrderingCorrect] at hc
      simp [merge, result, Nat.not_le_of_lt hc]

theorem run_correct (xs ys zs coins : List Bool)
    (hlen : coins.length = max xs.length ys.length + 1) :
    machine.run (cfg (some (encode .eq)) xs ys zs) coins =
      cfg none [] [] (decide (bitsValue xs ≤ bitsValue ys) :: zs) := by
  rw [run_scan .eq xs ys zs coins hlen, result_correct]

theorem haltsFromWithin (xs ys zs : List Bool) :
    Sequential.HaltsFromWithin machine (cfg (some (encode .eq)) xs ys zs)
      (max xs.length ys.length + 1) := by
  intro coins hcoins
  rw [run_correct xs ys zs coins hcoins]
  rfl

end KS.W28.LittleEndianCompare

end OAI
