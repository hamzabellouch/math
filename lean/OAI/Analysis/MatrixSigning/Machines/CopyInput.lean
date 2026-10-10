import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryMachine

namespace OAI

namespace KS.W29
namespace CopyInput

def reverseEntry (top : Nat) : Instruction 2 :=
  if top = 0 then ⟨some 1, .stay, .stay, .stay⟩
  else ⟨some 0, .pop, .stay, .push (top == 2)⟩

def copyEntry (top : Nat) : Instruction 2 :=
  if top = 0 then Instruction.halt 2
  else ⟨some 1, .push (top == 2), .push (top == 2), .pop⟩

def tableEntry (index : Nat) : Instruction 2 :=
  if index < 54 then reverseEntry (index / 2 % 3)
  else copyEntry (index / 18 % 3)

def machine : BinaryMachine :=
  ⟨2, 0, List.ofFn (fun i : Fin 108 => tableEntry i.val)⟩

def cfg (state : Option (Fin 2)) (input output scratch : List Bool) : Config 2 :=
  ⟨state, fun j => if j = 0 then input else if j = 1 then output else scratch⟩

theorem table_lookup (s : Fin 2) (c : Config 2) (b : Bool) :
    machine.table.getD (transitionIndex s c b) (Instruction.halt 2) =
      if s.val = 0 then reverseEntry (topCode (c.«stacks» 0))
      else copyEntry (topCode (c.«stacks» 2)) := by
  have hs := s.isLt
  have h₀ := topCode_lt_three (c.«stacks» 0)
  have h₁ := topCode_lt_three (c.«stacks» 1)
  have h₂ := topCode_lt_three (c.«stacks» 2)
  have hb : bitCode b < 2 := by cases b <;> decide
  have hi : transitionIndex s c b < 108 := transitionIndex_lt s c b
  have hc₀ : transitionIndex s c b / 2 % 3 = topCode (c.«stacks» 0) := by
    unfold transitionIndex headCode
    omega
  have hc₂ : transitionIndex s c b / 18 % 3 = topCode (c.«stacks» 2) := by
    unfold transitionIndex headCode
    omega
  have hphase : transitionIndex s c b < 54 ↔ s.val = 0 := by
    unfold transitionIndex headCode
    omega
  change (List.ofFn (fun i : Fin 108 => tableEntry i.val)).getD _ _ = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
  simp only [List.getElem_ofFn, tableEntry, hc₀, hc₂, hphase]

theorem reverse_step (x : Bool) (xs ys zs : List Bool) (b : Bool) :
    machine.step (cfg (some 0) (x :: xs) ys zs) b = cfg (some 0) xs ys (x :: zs) := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases x <;> change Config.mk (some (0 : Fin 2)) _ = Config.mk (some (0 : Fin 2)) _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem reverse_done (ys zs : List Bool) (b : Bool) :
    machine.step (cfg (some 0) [] ys zs) b = cfg (some 1) [] ys zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  change Config.mk (some (1 : Fin 2)) _ = Config.mk (some (1 : Fin 2)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem copy_step (x : Bool) (xs ys zs : List Bool) (b : Bool) :
    machine.step (cfg (some 1) xs ys (x :: zs)) b = cfg (some 1) (x :: xs) (x :: ys) zs := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  cases x <;> change Config.mk (some (1 : Fin 2)) _ = Config.mk (some (1 : Fin 2)) _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem copy_done (xs ys : List Bool) (b : Bool) :
    machine.step (cfg (some 1) xs ys []) b = cfg none xs ys [] := by
  simp only [BinaryMachine.step, cfg]
  erw [table_lookup]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_reverse (xs ys zs bits : List Bool) (hlen : bits.length = xs.length) :
    machine.run (cfg (some 0) xs ys zs) bits =
      cfg (some 0) [] ys (xs.reverse ++ zs) := by
  induction xs generalizing zs bits with
  | nil =>
      have hb : bits = [] := List.length_eq_zero_iff.mp hlen
      subst bits
      simp only [BinaryMachine.run, List.reverse_nil, List.nil_append]
      rfl
  | cons x xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons b bs =>
          have hbs : bs.length = xs.length := by simpa using hlen
          erw [BinaryMachine.run.eq_2, reverse_step, ih _ _ hbs]
          simp [List.reverse_cons, List.append_assoc]
          rfl

theorem run_copy (xs ys zs bits : List Bool) (hlen : bits.length = zs.length) :
    machine.run (cfg (some 1) xs ys zs) bits =
      cfg (some 1) (zs.reverse ++ xs) (zs.reverse ++ ys) [] := by
  induction zs generalizing xs ys bits with
  | nil =>
      have hb : bits = [] := List.length_eq_zero_iff.mp hlen
      subst bits
      simp only [BinaryMachine.run, List.reverse_nil, List.nil_append]
      rfl
  | cons z zs ih =>
      cases bits with
      | nil => simp at hlen
      | cons b bs =>
          have hbs : bs.length = zs.length := by simpa using hlen
          erw [BinaryMachine.run.eq_2, copy_step, ih _ _ _ hbs]
          simp [List.reverse_cons, List.append_assoc]
          rfl

theorem run_copy_input (xs left right : List Bool) (a b : Bool)
    (hl : left.length = xs.length) (hr : right.length = xs.length) :
    machine.run (cfg (some 0) xs [] []) (left ++ a :: (right ++ [b])) =
      cfg none xs xs [] := by
  erw [machine.run_append, run_reverse _ _ _ _ hl]
  simp only [List.append_nil, BinaryMachine.run]
  erw [reverse_done, machine.run_append, run_copy]
  · simp [BinaryMachine.run, copy_done]
    rfl
  · simpa using hr

theorem split_copy_fuel (bits : List Bool) (n : Nat) (h : bits.length = 2 * n + 2) :
    ∃ left a right b, bits = left ++ a :: (right ++ [b]) ∧
      left.length = n ∧ right.length = n := by
  have hn : n ≤ bits.length := by omega
  cases hd : bits.drop n with
  | nil =>
      have he := congrArg List.length hd
      simp only [List.length_drop, List.length_nil] at he
      omega
  | cons a tail =>
      have ht : tail.length = n + 1 := by
        have he := congrArg List.length hd
        simp only [List.length_drop, List.length_cons] at he
        omega
      cases he : tail.drop n with
      | nil =>
          have hz := congrArg List.length he
          simp only [List.length_drop, List.length_nil] at hz
          omega
      | cons b rest =>
          have hr : rest = [] := by
            apply List.length_eq_zero_iff.mp
            have hz := congrArg List.length he
            simp only [List.length_drop, List.length_cons] at hz
            omega
          subst rest
          refine ⟨bits.take n, a, tail.take n, b, ?_, ?_, ?_⟩
          · have hb : bits = bits.take n ++ a :: tail := by
              simpa [hd] using (List.take_append_drop n bits).symm
            have htail : tail = tail.take n ++ [b] := by
              simpa [he] using (List.take_append_drop n tail).symm
            calc
              bits = bits.take n ++ a :: tail := hb
              _ = bits.take n ++ a :: (tail.take n ++ [b]) :=
                congrArg (fun t => bits.take n ++ a :: t) htail
          · simp [List.length_take, Nat.min_eq_left hn]
          · simp [List.length_take, ht]

theorem run_eq_copy (xs bits : List Bool) (h : bits.length = 2 * xs.length + 2) :
    machine.run (machine.init xs) bits = cfg none xs xs [] := by
  obtain ⟨left, a, right, b, rfl, hl, hr⟩ := split_copy_fuel bits xs.length h
  have hi : machine.init xs = cfg (some 0) xs [] [] := by
    simp [BinaryMachine.init, cfg, machine]
  rw [hi]
  exact run_copy_input xs left right a b hl hr

theorem haltsWithin (xs : List Bool) : machine.HaltsWithin xs (2 * xs.length + 2) := by
  rw [machine.haltsWithin_iff_bitLists]
  intro bits hb
  rw [run_eq_copy xs bits hb]
  rfl

theorem output_eq (xs bits : List Bool) (h : bits.length = 2 * xs.length + 2) :
    machine.output xs bits = xs := by
  unfold BinaryMachine.output
  rw [run_eq_copy xs bits h]
  rfl

theorem haltsWithin_polynomialFuel (xs : List Bool) :
    machine.HaltsWithin xs (polynomialFuel 2 1 xs.length) := by
  have h : polynomialFuel 2 1 xs.length = 2 * xs.length + 2 := by
    simp [polynomialFuel, Nat.mul_add]
  rw [h]
  exact haltsWithin xs

end CopyInput
end KS.W29

end OAI
