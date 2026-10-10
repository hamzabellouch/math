import OAI.Computability.MeanPayoff.SignedBits

namespace OAI

section
namespace MeanPayoff.WorkStack.SignedAddition
open BinaryStack (Op applyOp)
open BinaryStack.Addition (low carry)
open SignedBits (Word)

inductive Label where
  | start
  | feed (a b c : Bool)
  | transfer (s : Bool)
  | halt
  deriving DecidableEq, Fintype

noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem decode (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply _

noncomputable def program : Program where
  states := Fintype.card Label
  start := enc .start
  transition q top _ :=
    match equiv.symm q with
    | .start => some ⟨enc (.feed ((top 0).getD false) ((top 1).getD false) false), ![.pop, .pop, .keep]⟩
    | .feed a b c =>
      if top 0 = none ∧ top 1 = none then
        some ⟨enc (.transfer (SignedBits.finalSign a b c)), ![.keep, .keep, .push (low a b c)]⟩
      else
        let x := (top 0).getD a
        let y := (top 1).getD b
        some ⟨enc (.feed a b (carry x y c)), ![.pop, .pop, .push (low x y c)]⟩
    | .transfer s =>
      match top 2 with
      | none => some ⟨enc .halt, ![.push s, .keep, .keep]⟩
      | some b => some ⟨enc (.transfer s), ![.push b, .keep, .pop]⟩
    | .halt => none

noncomputable def state (q : Label) (xs ys zs : List Bool) : Config program :=
  ⟨some (enc q), ![xs, ys, zs]⟩
def stopped (xs ys : List Bool) : Config program := ⟨none, ![xs, ys, []]⟩

@[simp] theorem step_start (a b : Bool) (xs ys zs : List Bool) (bit : Bool) :
    step program (state .start (a :: xs) (b :: ys) zs) bit = state (.feed a b false) xs ys zs := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_nil (a b c : Bool) (zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) [] [] zs) bit =
      state (.transfer (SignedBits.finalSign a b c)) [] [] (low a b c :: zs) := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_left (a b c x : Bool) (xs zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) (x :: xs) [] zs) bit =
      state (.feed a b (carry x b c)) xs [] (low x b c :: zs) := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_right (a b c y : Bool) (ys zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) [] (y :: ys) zs) bit =
      state (.feed a b (carry a y c)) [] ys (low a y c :: zs) := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_both (a b c x y : Bool) (xs ys zs : List Bool) (bit : Bool) :
    step program (state (.feed a b c) (x :: xs) (y :: ys) zs) bit =
      state (.feed a b (carry x y c)) xs ys (low x y c :: zs) := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_transfer_cons (s b : Bool) (xs ys zs : List Bool) (bit : Bool) :
    step program (state (.transfer s) xs ys (b :: zs)) bit = state (.transfer s) (b :: xs) ys zs := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_transfer_nil (s : Bool) (xs ys : List Bool) (bit : Bool) :
    step program (state (.transfer s) xs ys []) bit = state .halt (s :: xs) ys [] := by
  simp only [step, state, program, decode]
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_halt (xs ys : List Bool) (bit : Bool) :
    step program (state .halt xs ys []) bit = stopped xs ys := by
  simp only [step, state, program, decode]; rfl

theorem feed_runs (a b c : Bool) (xs ys zs : List Bool) (bits : ℕ → Bool) :
    advance program bits (state (.feed a b c) xs ys zs) (max xs.length ys.length + 1) =
      state (.transfer (SignedBits.add a b c xs ys).sign) [] []
        ((SignedBits.add a b c xs ys).digits.reverse ++ zs) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp [advance, SignedBits.add]
    | cons y ys =>
      rw [show max [].length (y :: ys).length + 1 = max [].length ys.length + 1 + 1 by simp,
        advance_front, step_feed_right, feed_runs]
      simp only [SignedBits.add, SignedBits.cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
  | cons x xs =>
    cases ys with
    | nil =>
      rw [show max (x :: xs).length [].length + 1 = max xs.length [].length + 1 + 1 by simp,
        advance_front, step_feed_left, feed_runs]
      simp only [SignedBits.add, SignedBits.cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
    | cons y ys =>
      rw [show max (x :: xs).length (y :: ys).length + 1 = max xs.length ys.length + 1 + 1 by simp,
        advance_front, step_feed_both, feed_runs]
      simp only [SignedBits.add, SignedBits.cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
termination_by xs.length + ys.length

theorem transfer_runs (s : Bool) (xs ys zs : List Bool) (bits : ℕ → Bool) :
    advance program bits (state (.transfer s) xs ys zs) (zs.length + 2) =
      stopped (s :: (zs.reverse ++ xs)) ys := by
  induction zs generalizing xs bits with
  | nil => simp [advance]
  | cons b zs ih =>
    rw [show (b :: zs).length + 2 = zs.length + 2 + 1 by simp,
      advance_front, step_transfer_cons, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem program_adds (a b : Bool) (xs ys : List Bool) (bits : ℕ → Bool) :
    advance program bits (state .start (a :: xs) (b :: ys) [])
      (2 * max xs.length ys.length + 5) =
      stopped ((SignedBits.add a b false xs ys).sign ::
        (SignedBits.add a b false xs ys).digits) [] := by
  rw [show 2 * max xs.length ys.length + 5 = (2 * max xs.length ys.length + 4) + 1 by omega,
    advance_front, step_start]
  rw [show 2 * max xs.length ys.length + 4 = (max xs.length ys.length + 1) +
    ((SignedBits.add a b false xs ys).digits.length + 2) by rw [SignedBits.add_length]; omega,
    advance_add, feed_runs]
  simp only [List.append_nil]
  have h := transfer_runs (SignedBits.add a b false xs ys).sign [] []
    (SignedBits.add a b false xs ys).digits.reverse
    (fun j => bits (max xs.length ys.length + 1 + j + 1))
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil] using h

end MeanPayoff.WorkStack.SignedAddition
namespace MeanPayoff
namespace MachineRun

def advance (M : Machine) (bits : ℕ → Bool) (c : Configuration M) : ℕ → Configuration M
  | 0 => c
  | t + 1 => step M (advance M bits c t) (bits t)

@[simp] theorem advance_zero (M : Machine) (bits : ℕ → Bool) (c : Configuration M) :
    advance M bits c 0 = c := rfl

theorem advance_front (M : Machine) (bits : ℕ → Bool) (c : Configuration M) (t : ℕ) :
    advance M bits c (t + 1) = advance M (fun j => bits (j + 1)) (step M c (bits 0)) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [advance, ih]; rfl

theorem advance_add (M : Machine) (bits : ℕ → Bool) (c : Configuration M) (t u : ℕ) :
    advance M bits c (t + u) = advance M (fun j => bits (t + j)) (advance M bits c t) u := by
  induction u with
  | zero => rfl
  | succ u ih => change step M (advance M bits c (t + u)) (bits (t + u)) = _; rw [ih]; rfl

@[simp] theorem advance_initial (M : Machine) (bits : ℕ → Bool) (code : List Bool) (t : ℕ) :
    advance M bits (initial M code) t = run M code bits t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [advance, ih]; rfl

theorem advance_halted (M : Machine) (bits : ℕ → Bool) (c : Configuration M)
    (hc : c.control = none) (t : ℕ) : advance M bits c t = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [advance, ih]; simp only [step, hc]

theorem first_termination (M : Machine) (bits : ℕ → Bool) (c : Configuration M) (T : ℕ)
    (hT : (advance M bits c T).control = none) :
    ∃ t ≤ T, advance M bits c t = advance M bits c T ∧
      ∀ j < t, (advance M bits c j).control ≠ none := by
  have hex : ∃ t, (advance M bits c t).control = none := ⟨T, hT⟩
  let t := Nat.find hex
  have ht : (advance M bits c t).control = none := Nat.find_spec hex
  have hle : t ≤ T := Nat.find_min' hex hT
  refine ⟨t, hle, ?_, fun j hj => Nat.find_min hex hj⟩
  symm
  rw [show T = t + (T - t) by omega, advance_add, advance_halted M _ _ ht]

namespace Sequence
abbrev Labels (P Q : Machine) := Fin P.states ⊕ Fin Q.states
noncomputable def equiv (P Q : Machine) : Labels P Q ≃ Fin (Fintype.card (Labels P Q)) :=
  Fintype.equivFin _
noncomputable def lhs (P Q : Machine) (q : Fin P.states) := equiv P Q (.inl q)
noncomputable def rhs (P Q : Machine) (q : Fin Q.states) := equiv P Q (.inr q)

noncomputable def machine (P Q : Machine) : Machine where
  states := Fintype.card (Labels P Q)
  start := lhs P Q P.start
  transition q top bit :=
    match (equiv P Q).symm q with
    | .inl q =>
      match P.transition q top bit with
      | none => some ⟨rhs P Q Q.start, top, fun _ => .stay⟩
      | some a => some ⟨lhs P Q a.next, a.write, a.shift⟩
    | .inr q => (Q.transition q top bit).map fun a => ⟨rhs P Q a.next, a.write, a.shift⟩

noncomputable def left (P Q : Machine) (c : Configuration P) : Configuration (machine P Q) :=
  ⟨some (match c.control with | none => rhs P Q Q.start | some q => lhs P Q q), c.head, c.tape⟩
noncomputable def restart (P Q : Machine) (c : Configuration P) : Configuration Q :=
  ⟨some Q.start, c.head, c.tape⟩
noncomputable def right (P Q : Machine) (c : Configuration Q) : Configuration (machine P Q) :=
  ⟨c.control.map (rhs P Q), c.head, c.tape⟩

@[simp] theorem decode_lhs (P Q : Machine) (q : Fin P.states) :
    (equiv P Q).symm (lhs P Q q) = .inl q := (equiv P Q).symm_apply_apply _
@[simp] theorem decode_rhs (P Q : Machine) (q : Fin Q.states) :
    (equiv P Q).symm (rhs P Q q) = .inr q := (equiv P Q).symm_apply_apply _

theorem step_left (P Q : Machine) (c : Configuration P) (hc : c.control ≠ none) (bit : Bool) :
    step (machine P Q) (left P Q c) bit = left P Q (step P c bit) := by
  rcases c with ⟨q, h, xs⟩
  cases q with
  | none => exact (hc rfl).elim
  | some q =>
    simp only [step, left, machine, decode_lhs]
    cases ha : P.transition q (fun k => xs k (h k)) bit with
    | none =>
      apply BinaryStack.concrete_ext
      · rfl
      · funext k; simp [Direction.offset]
      · funext k; exact Function.update_eq_self _ _
    | some a => rfl

theorem step_right (P Q : Machine) (c : Configuration Q) (bit : Bool) :
    step (machine P Q) (right P Q c) bit = right P Q (step Q c bit) := by
  rcases c with ⟨q, h, xs⟩
  cases q with
  | none => rfl
  | some q =>
    simp only [step, right, machine, Option.map_some, decode_rhs]
    cases Q.transition q (fun k => xs k (h k)) bit <;> rfl

theorem advance_left (P Q : Machine) (c : Configuration P) (bits : ℕ → Bool) (t : ℕ)
    (ht : ∀ j < t, (advance P bits c j).control ≠ none) :
    advance (machine P Q) bits (left P Q c) t = left P Q (advance P bits c t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [advance, ih (fun j hj => ht j (by omega)), step_left P Q _ (ht t (by omega))]; rfl

theorem advance_right (P Q : Machine) (c : Configuration Q) (bits : ℕ → Bool) (t : ℕ) :
    advance (machine P Q) bits (right P Q c) t = right P Q (advance Q bits c t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [advance, ih, step_right]; rfl

@[simp] theorem left_initial (P Q : Machine) (code : List Bool) :
    left P Q (initial P code) = initial (machine P Q) code := rfl

theorem run_after_first_halt (P Q : Machine) (code : List Bool) (bits : ℕ → Bool) (t u : ℕ)
    (ht : ∀ j < t, (run P code bits j).control ≠ none) (hh : (run P code bits t).control = none) :
    run (machine P Q) code bits (t + u) =
      right P Q (advance Q (fun j => bits (t + j)) (restart P Q (run P code bits t)) u) := by
  rw [← advance_initial, ← left_initial, advance_add,
    advance_left P Q _ bits t (by simpa only [advance_initial] using ht), advance_initial]
  have he : left P Q (run P code bits t) = right P Q (restart P Q (run P code bits t)) := by
    simp only [left, hh, right, restart]; rfl
  rw [he, advance_right]

end Sequence
end MachineRun
end MeanPayoff
end

end OAI
