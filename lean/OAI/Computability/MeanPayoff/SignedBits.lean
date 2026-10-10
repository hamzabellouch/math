import OAI.Computability.MeanPayoff.Simulation

namespace OAI

section
namespace MeanPayoff.WorkStack
open BinaryStack (Op applyOp)
namespace Addition
open BinaryStack.Addition (low carry add value add_value)

def finiteProgram : Program where
  states := 3
  start := 0
  transition q top _ :=
    if q = 2 then
      (top 2).map fun b => ⟨2, ![.push b, .keep, .pop]⟩
    else if top 0 = none ∧ top 1 = none then
      some ⟨2, ![.keep, .keep, if q = 1 then .push true else .keep]⟩
    else
      let a := (top 0).getD false
      let b := (top 1).getD false
      let c := decide (q = 1)
      some ⟨if carry a b c then 1 else 0, ![.pop, .pop, .push (low a b c)]⟩

def label (c : Bool) : Fin 3 := if c then 1 else 0

def feed (c : Bool) (xs ys zs : List Bool) : Config finiteProgram :=
  ⟨some (label c), ![xs, ys, zs]⟩
def transfer (xs ys zs : List Bool) : Config finiteProgram :=
  ⟨some (2 : Fin 3), ![xs, ys, zs]⟩
def stopped (xs ys : List Bool) : Config finiteProgram :=
  ⟨none, ![xs, ys, []]⟩

@[simp] theorem step_feed_nil (c : Bool) (zs : List Bool) (bit : Bool) :
    step finiteProgram (feed c [] [] zs) bit =
      transfer [] [] (if c then true :: zs else zs) := by
  cases c <;> apply Config.ext <;> try rfl
  all_goals funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_left (c a : Bool) (as zs : List Bool) (bit : Bool) :
    step finiteProgram (feed c (a :: as) [] zs) bit =
      feed (carry a false c) as [] (low a false c :: zs) := by
  cases c <;> apply Config.ext <;> try rfl
  all_goals funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_right (c b : Bool) (bs zs : List Bool) (bit : Bool) :
    step finiteProgram (feed c [] (b :: bs) zs) bit =
      feed (carry false b c) [] bs (low false b c :: zs) := by
  cases c <;> apply Config.ext <;> try rfl
  all_goals funext k; fin_cases k <;> rfl

@[simp] theorem step_feed_both (c a b : Bool) (as bs zs : List Bool) (bit : Bool) :
    step finiteProgram (feed c (a :: as) (b :: bs) zs) bit =
      feed (carry a b c) as bs (low a b c :: zs) := by
  cases c <;> apply Config.ext <;> try rfl
  all_goals funext k; fin_cases k <;> rfl

@[simp] theorem step_transfer_cons (xs ys zs : List Bool) (b bit : Bool) :
    step finiteProgram (transfer xs ys (b :: zs)) bit = transfer (b :: xs) ys zs := by
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl

@[simp] theorem step_transfer_nil (xs ys : List Bool) (bit : Bool) :
    step finiteProgram (transfer xs ys []) bit = stopped xs ys := rfl

theorem feed_adds (c : Bool) (xs ys zs : List Bool) (bits : ℕ → Bool) :
    advance finiteProgram bits (feed c xs ys zs) (max xs.length ys.length + 1) =
      transfer [] [] ((add c xs ys).reverse ++ zs) := by
  cases xs with
  | nil =>
    cases ys with
    | nil =>
      cases c <;> simp [advance, step_feed_nil, add]
    | cons b bs =>
      rw [show max [].length (b :: bs).length + 1 = (max [].length bs.length + 1) + 1 by simp]
      rw [advance_front, step_feed_right, feed_adds]
      simp only [add, List.reverse_cons, List.append_assoc, List.singleton_append]
  | cons a as =>
    cases ys with
    | nil =>
      rw [show max (a :: as).length [].length + 1 = (max as.length [].length + 1) + 1 by simp]
      rw [advance_front, step_feed_left, feed_adds]
      simp only [add, List.reverse_cons, List.append_assoc, List.singleton_append]
    | cons b bs =>
      rw [show max (a :: as).length (b :: bs).length + 1 = (max as.length bs.length + 1) + 1 by simp]
      rw [advance_front, step_feed_both, feed_adds]
      simp only [add, List.reverse_cons, List.append_assoc, List.singleton_append]
termination_by xs.length + ys.length

theorem transfer_runs (xs ys zs : List Bool) (bits : ℕ → Bool) :
    advance finiteProgram bits (transfer xs ys zs) (zs.length + 1) =
      stopped (zs.reverse ++ xs) ys := by
  induction zs generalizing xs bits with
  | nil => simp [advance]
  | cons b zs ih =>
    rw [List.length_cons, Nat.add_assoc, show 1 + 1 = 1 + 1 from rfl,
      ← Nat.add_assoc, advance_front, step_transfer_cons, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem add_length (c : Bool) (xs ys : List Bool) :
    (add c xs ys).length ≤ max xs.length ys.length + 1 := by
  cases xs with
  | nil =>
    cases ys with
    | nil => cases c <;> simp [add]
    | cons b bs =>
      rw [add, List.length_cons]
      have h := add_length (carry false b c) [] bs
      simp only [List.length_nil, List.length_cons, max_eq_right (Nat.zero_le _)] at *
      omega
  | cons a as =>
    cases ys with
    | nil =>
      rw [add, List.length_cons]
      have h := add_length (carry a false c) as []
      simp only [List.length_nil, List.length_cons, max_eq_left (Nat.zero_le _)] at *
      omega
    | cons b bs =>
      rw [add, List.length_cons]
      have h := add_length (carry a b c) as bs
      simp only [List.length_cons, Nat.succ_max_succ] at *
      omega
termination_by xs.length + ys.length

theorem program_adds_exact (c : Bool) (xs ys : List Bool) (bits : ℕ → Bool) :
    advance finiteProgram bits (feed c xs ys [])
      (max xs.length ys.length + 1 + ((add c xs ys).length + 1)) =
      stopped (add c xs ys) [] := by
  rw [advance_add, feed_adds]
  simp only [List.append_nil]
  have h := transfer_runs [] [] ((add c xs ys).reverse)
    (fun j => bits (max xs.length ys.length + 1 + j))
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil] using h

theorem program_adds_bounded (c : Bool) (xs ys : List Bool) (bits : ℕ → Bool) :
    advance finiteProgram bits (feed c xs ys []) (2 * max xs.length ys.length + 3) =
      stopped (add c xs ys) [] := by
  let t := max xs.length ys.length + 1 + ((add c xs ys).length + 1)
  have ht : t ≤ 2 * max xs.length ys.length + 3 := by
    have h := add_length c xs ys
    dsimp only [t]; omega
  rw [show 2 * max xs.length ys.length + 3 = t + (2 * max xs.length ys.length + 3 - t) by omega,
    advance_add, program_adds_exact]
  exact advance_halted _ _ _ rfl _

theorem result_value (c : Bool) (xs ys : List Bool) (bits : ℕ → Bool) :
    let r := advance finiteProgram bits (feed c xs ys []) (2 * max xs.length ys.length + 3)
    r.control = none ∧ value (r.stack 0) = value xs + value ys + c.toNat ∧
      r.stack 1 = [] ∧ r.stack 2 = [] := by
  simp [program_adds_bounded, stopped, add_value]

end Addition
end MeanPayoff.WorkStack
namespace MeanPayoff.WorkStack
open BinaryStack (Op applyOp)

def Computes (P : Program) (f : (Fin 3 → List Bool) → (Fin 3 → List Bool))
    (time : (Fin 3 → List Bool) → ℕ) : Prop :=
  ∀ xs bits, ∃ t ≤ time xs,
    advance P bits ⟨some P.start, xs⟩ t = ⟨none, f xs⟩

namespace Sequence
abbrev Labels (P Q : Program) := Fin P.states ⊕ Fin Q.states
noncomputable def equiv (P Q : Program) : Labels P Q ≃ Fin (Fintype.card (Labels P Q)) :=
  Fintype.equivFin _
noncomputable def lhs (P Q : Program) (q : Fin P.states) := equiv P Q (.inl q)
noncomputable def rhs (P Q : Program) (q : Fin Q.states) := equiv P Q (.inr q)

noncomputable def program (P Q : Program) : Program where
  states := Fintype.card (Labels P Q)
  start := lhs P Q P.start
  transition q top bit :=
    match (equiv P Q).symm q with
    | .inl q =>
      match P.transition q top bit with
      | none => some ⟨rhs P Q Q.start, fun _ => .keep⟩
      | some a => some ⟨lhs P Q a.next, a.work⟩
    | .inr q => (Q.transition q top bit).map fun a => ⟨rhs P Q a.next, a.work⟩

noncomputable def left (P Q : Program) (c : Config P) : Config (program P Q) :=
  ⟨some (match c.control with | none => rhs P Q Q.start | some q => lhs P Q q), c.stack⟩
noncomputable def right (P Q : Program) (c : Config Q) : Config (program P Q) :=
  ⟨c.control.map (rhs P Q), c.stack⟩

@[simp] theorem decode_lhs (P Q : Program) (q : Fin P.states) :
    (equiv P Q).symm (lhs P Q q) = .inl q := (equiv P Q).symm_apply_apply _
@[simp] theorem decode_rhs (P Q : Program) (q : Fin Q.states) :
    (equiv P Q).symm (rhs P Q q) = .inr q := (equiv P Q).symm_apply_apply _

theorem step_left (P Q : Program) (c : Config P) (hc : c.control ≠ none) (bit : Bool) :
    step (program P Q) (left P Q c) bit = left P Q (step P c bit) := by
  rcases c with ⟨q, xs⟩
  cases q with
  | none => exact (hc rfl).elim
  | some q =>
    simp only [step, left, program, decode_lhs]
    cases P.transition q (fun k => (xs k).head?) bit <;> rfl

theorem step_right (P Q : Program) (c : Config Q) (bit : Bool) :
    step (program P Q) (right P Q c) bit = right P Q (step Q c bit) := by
  rcases c with ⟨q, xs⟩
  cases q with
  | none => rfl
  | some q =>
    simp only [step, right, program, Option.map_some, decode_rhs]
    cases Q.transition q (fun k => (xs k).head?) bit <;> rfl

theorem advance_left (P Q : Program) (c : Config P) (bits : ℕ → Bool) (t : ℕ)
    (ht : ∀ j < t, (advance P bits c j).control ≠ none) :
    advance (program P Q) bits (left P Q c) t = left P Q (advance P bits c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [advance, ih (fun j hj => ht j (by omega)), step_left P Q _ (ht t (by omega))]
    rfl

theorem advance_right (P Q : Program) (c : Config Q) (bits : ℕ → Bool) (t : ℕ) :
    advance (program P Q) bits (right P Q c) t = right P Q (advance Q bits c t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [advance, ih, step_right]; rfl

end Sequence

theorem first_termination (P : Program) (c : Config P) (bits : ℕ → Bool) (T : ℕ)
    (ys : Fin 3 → List Bool) (hT : advance P bits c T = ⟨none, ys⟩) :
    ∃ t ≤ T, advance P bits c t = ⟨none, ys⟩ ∧
      ∀ j < t, (advance P bits c j).control ≠ none := by
  have hex : ∃ t, (advance P bits c t).control = none := ⟨T, by rw [hT]⟩
  let t := Nat.find hex
  have ht : (advance P bits c t).control = none := Nat.find_spec hex
  have hle : t ≤ T := Nat.find_min' hex (by rw [hT])
  refine ⟨t, hle, ?_, ?_⟩
  · have hh : advance P bits c T = advance P bits c t := by
      rw [show T = t + (T - t) by omega, advance_add, advance_halted P _ _ ht]
    exact hh.symm.trans hT
  · exact fun j hj => Nat.find_min hex hj

theorem Computes.sequence {P Q : Program}
    {f g : (Fin 3 → List Bool) → (Fin 3 → List Bool)}
    {a b : (Fin 3 → List Bool) → ℕ}
    (hP : Computes P f a) (hQ : Computes Q g b) :
    Computes (Sequence.program P Q) (g ∘ f) (fun xs => a xs + b (f xs)) := by
  intro xs bits
  obtain ⟨T, hT, hp⟩ := hP xs bits
  obtain ⟨t, ht, he, ha⟩ := first_termination P ⟨some P.start, xs⟩ bits T (f xs) hp
  obtain ⟨u, hu, hq⟩ := hQ (f xs) (fun j => bits (t + j))
  refine ⟨t + u, by dsimp only; omega, ?_⟩
  change advance (Sequence.program P Q) bits (Sequence.left P Q ⟨some P.start, xs⟩) (t + u) = _
  rw [advance_add, Sequence.advance_left P Q _ bits t ha, he]
  change advance (Sequence.program P Q) (fun j => bits (t + j))
    (Sequence.right P Q ⟨some Q.start, f xs⟩) u = _
  rw [Sequence.advance_right, hq]
  rfl

end MeanPayoff.WorkStack
namespace MeanPayoff
namespace SignedBits
open BinaryStack.Addition (value low carry full_adder)

structure Word where
  sign : Bool
  digits : List Bool
  deriving DecidableEq

def Word.val (w : Word) : ℤ := (value w.digits : ℤ) - if w.sign then (2 : ℤ) ^ w.digits.length else 0

def cons (b : Bool) (w : Word) : Word := ⟨w.sign, b :: w.digits⟩

def head (s : Bool) (xs : List Bool) : Bool := xs.head?.getD s

@[simp] theorem val_cons (b : Bool) (w : Word) :
    (cons b w).val = b.toNat + 2 * w.val := by
  cases w with
  | mk s xs =>
    cases s <;> simp [Word.val, cons, value, pow_succ] ; ring

theorem val_uncons (s : Bool) (xs : List Bool) :
    (Word.mk s xs).val = (head s xs).toNat + 2 * (Word.mk s xs.tail).val := by
  cases xs with
  | nil => cases s <;> norm_num [Word.val, head, value]
  | cons b bs => exact val_cons b ⟨s, bs⟩

def finalSign (a b c : Bool) : Bool := if a = b then a else !c

def add (a b c : Bool) : List Bool → List Bool → Word
  | [], [] => ⟨finalSign a b c, [low a b c]⟩
  | x :: xs, [] => cons (low x b c) (add a b (carry x b c) xs [])
  | [], y :: ys => cons (low a y c) (add a b (carry a y c) [] ys)
  | x :: xs, y :: ys => cons (low x y c) (add a b (carry x y c) xs ys)
termination_by xs ys => xs.length + ys.length

theorem add_val (a b c : Bool) (xs ys : List Bool) :
    (add a b c xs ys).val = (Word.mk a xs).val + (Word.mk b ys).val + c.toNat := by
  cases xs with
  | nil =>
    cases ys with
    | nil => cases a <;> cases b <;> cases c <;> norm_num [add, Word.val, value, low, finalSign]
    | cons y ys =>
      rw [add, val_cons, add_val]
      have hx := val_uncons a []
      have hy := val_uncons b (y :: ys)
      have hh := full_adder a y c
      simp only [head, List.head?_nil, List.head?_cons, Option.getD_none, Option.getD_some,
        List.tail_nil, List.tail_cons] at hx hy
      have hh' : ((low a y c).toNat : ℤ) + 2 * (carry a y c).toNat = a.toNat + y.toNat + c.toNat := by
        exact_mod_cast hh
      omega
  | cons x xs =>
    cases ys with
    | nil =>
      rw [add, val_cons, add_val]
      have hx := val_uncons a (x :: xs)
      have hy := val_uncons b []
      have hh := full_adder x b c
      simp only [head, List.head?_nil, List.head?_cons, Option.getD_none, Option.getD_some,
        List.tail_nil, List.tail_cons] at hx hy
      have hh' : ((low x b c).toNat : ℤ) + 2 * (carry x b c).toNat = x.toNat + b.toNat + c.toNat := by
        exact_mod_cast hh
      omega
    | cons y ys =>
      rw [add, val_cons, add_val]
      have hx := val_uncons a (x :: xs)
      have hy := val_uncons b (y :: ys)
      have hh := full_adder x y c
      simp only [head, List.head?_cons, Option.getD_some, List.tail_cons] at hx hy
      have hh' : ((low x y c).toNat : ℤ) + 2 * (carry x y c).toNat = x.toNat + y.toNat + c.toNat := by
        exact_mod_cast hh
      omega
termination_by xs.length + ys.length

theorem add_length (a b c : Bool) (xs ys : List Bool) :
    (add a b c xs ys).digits.length = max xs.length ys.length + 1 := by
  cases xs with
  | nil =>
    cases ys with
    | nil => rw [add]; rfl
    | cons y ys =>
      rw [add]
      change (add a b (carry a y c) [] ys).digits.length + 1 = _
      rw [add_length a b (carry a y c) [] ys]
      simp
  | cons x xs =>
    cases ys with
    | nil =>
      rw [add]
      change (add a b (carry x b c) xs []).digits.length + 1 = _
      rw [add_length a b (carry x b c) xs []]
      simp
    | cons y ys =>
      rw [add]
      change (add a b (carry x y c) xs ys).digits.length + 1 = _
      rw [add_length a b (carry x y c) xs ys]
      simp only [List.length_cons, Nat.succ_max_succ]
termination_by xs.length + ys.length

theorem value_bound (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b <;> simp only [value, Bool.toNat_false, Bool.toNat_true, List.length_cons, pow_succ] <;> omega

theorem val_negative (w : Word) : w.val < 0 ↔ w.sign = true := by
  cases w with
  | mk s xs =>
    have h : (value xs : ℤ) < 2 ^ xs.length := by exact_mod_cast value_bound xs
    cases s <;> simp [Word.val] ; omega

end SignedBits
end MeanPayoff
end

end OAI
