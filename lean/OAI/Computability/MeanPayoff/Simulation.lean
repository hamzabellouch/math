import OAI.Computability.MeanPayoff.BitProgram

namespace OAI

section
namespace MeanPayoff
namespace BinaryStack

def advance (P : Program) (bits : ℕ → Bool) (c : Config P) : ℕ → Config P
  | 0 => c
  | t + 1 => step P (advance P bits c t) (bits t)

theorem advance_front (P : Program) (bits : ℕ → Bool) (c : Config P) (t : ℕ) :
    advance P bits c (t + 1) = advance P (fun j => bits (j + 1)) (step P c (bits 0)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step P (advance P bits c (t + 1)) (bits (t + 1)) =
      step P (advance P (fun j => bits (j + 1)) (step P c (bits 0)) t) (bits (t + 1))
    rw [ih]

theorem advance_halted (P : Program) (bits : ℕ → Bool) (c : Config P)
    (hc : c.control = none) (t : ℕ) : advance P bits c t = c := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [advance, ih, step, hc]

@[ext] theorem Config.ext {P : Program} {a b : Config P}
    (hc : a.control = b.control) (hs : a.stack = b.stack) (ho : a.output = b.output) : a = b := by
  cases a; cases b; simp_all

namespace Addition

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

def low (a b c : Bool) : Bool := xor (xor a b) c
def carry (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem full_adder (a b c : Bool) :
    (low a b c).toNat + 2 * (carry a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

def add : Bool → List Bool → List Bool → List Bool
  | c, [], [] => if c then [true] else []
  | c, a :: as, [] => low a false c :: add (carry a false c) as []
  | c, [], b :: bs => low false b c :: add (carry false b c) [] bs
  | c, a :: as, b :: bs => low a b c :: add (carry a b c) as bs
termination_by _ xs ys => xs.length + ys.length

theorem add_value (c : Bool) (xs ys : List Bool) :
    value (add c xs ys) = value xs + value ys + c.toNat := by
  cases xs with
  | nil =>
    cases ys with
    | nil => rw [add]; cases c <;> simp [value]
    | cons b bs =>
      rw [add]
      simp only [value]
      rw [add_value]
      have he := full_adder false b c
      simp only [value, Bool.toNat_false] at *
      omega
  | cons a as =>
    cases ys with
    | nil =>
      rw [add]
      simp only [value]
      rw [add_value]
      have he := full_adder a false c
      simp only [value, Bool.toNat_false] at *
      omega
    | cons b bs =>
      rw [add]
      simp only [value]
      rw [add_value]
      have he := full_adder a b c
      omega
termination_by xs.length + ys.length

def label : Bool → Fin 2
  | false => 0
  | true => 1

def finiteProgram : Program where
  states := 2
  start := 0
  transition q top _ :=
    if top 0 = none ∧ top 1 = none then
      if q = 1 then some ⟨0, fun _ => Op.keep, some true⟩ else none
    else
      let a := (top 0).getD false
      let b := (top 1).getD false
      let c := decide (q = 1)
      some ⟨label (carry a b c), fun _ => Op.pop, some (low a b c)⟩

def state (c : Bool) (xs ys out : List Bool) : Config finiteProgram :=
  ⟨some (label c), ![xs, ys], out⟩

def stopped (out : List Bool) : Config finiteProgram :=
  ⟨none, fun _ => [], out⟩

@[simp] theorem label_one (c : Bool) : decide (label c = 1) = c := by
  cases c <;> rfl

@[simp] theorem step_nil_false (out : List Bool) (bit : Bool) :
    step finiteProgram (state false [] [] out) bit = stopped out := by
  apply Config.ext
  · rfl
  · funext k; fin_cases k <;> rfl
  · rfl

@[simp] theorem step_nil_true (out : List Bool) (bit : Bool) :
    step finiteProgram (state true [] [] out) bit = state false [] [] (out ++ [true]) := by
  rfl

@[simp] theorem step_cons_left (c a : Bool) (as out : List Bool) (bit : Bool) :
    step finiteProgram (state c (a :: as) [] out) bit =
      state (carry a false c) as [] (out ++ [low a false c]) := by
  cases c <;> apply Config.ext <;> try rfl
  all_goals funext k; fin_cases k <;> rfl

@[simp] theorem step_cons_right (c b : Bool) (bs out : List Bool) (bit : Bool) :
    step finiteProgram (state c [] (b :: bs) out) bit =
      state (carry false b c) [] bs (out ++ [low false b c]) := by
  cases c <;> apply Config.ext <;> try rfl
  all_goals funext k; fin_cases k <;> rfl

@[simp] theorem step_cons_both (c a b : Bool) (as bs out : List Bool) (bit : Bool) :
    step finiteProgram (state c (a :: as) (b :: bs) out) bit =
      state (carry a b c) as bs (out ++ [low a b c]) := by
  cases c <;> apply Config.ext <;> try rfl
  all_goals funext k; fin_cases k <;> rfl

theorem program_adds (c : Bool) (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance finiteProgram bits (state c xs ys out) (max xs.length ys.length + 2) =
      stopped (out ++ add c xs ys) := by
  cases xs with
  | nil =>
    cases ys with
    | nil =>
      cases c <;> simp only [List.length_nil, max_self, Nat.zero_add, advance, step_nil_true, step_nil_false, add, Bool.false_eq_true, ↓reduceIte,
        List.append_nil]
      · rfl
    | cons b bs =>
      rw [show max [].length (b :: bs).length + 2 = max [].length bs.length + 2 + 1 by simp]
      rw [advance_front, step_cons_right, program_adds]
      simp [add, List.append_assoc]
  | cons a as =>
    cases ys with
    | nil =>
      rw [show max (a :: as).length [].length + 2 = max as.length [].length + 2 + 1 by simp]
      rw [advance_front, step_cons_left, program_adds]
      simp [add, List.append_assoc]
    | cons b bs =>
      rw [show max (a :: as).length (b :: bs).length + 2 = max as.length bs.length + 2 + 1 by simp]
      rw [advance_front, step_cons_both, program_adds]
      simp [add, List.append_assoc]
termination_by xs.length + ys.length

end Addition
end BinaryStack

namespace WorkStack
open BinaryStack (Op applyOp shiftOp firstWrite pendingWrite cells cells_top cells_applyOp concrete_ext)

structure Act (q : ℕ) where
  next : Fin q
  work : Fin 3 → Op

structure Program where
  states : ℕ
  start : Fin states
  transition : Fin states → (Fin 3 → Option Bool) → Bool → Option (Act states)

structure Config (P : Program) where
  control : Option (Fin P.states)
  stack : Fin 3 → List Bool

@[ext] theorem Config.ext {P : Program} {a b : Config P}
    (hc : a.control = b.control) (hs : a.stack = b.stack) : a = b := by
  cases a; cases b; simp_all

def step (P : Program) (c : Config P) (bit : Bool) : Config P :=
  match c.control with
  | none => c
  | some q =>
    match P.transition q (fun k => (c.stack k).head?) bit with
    | none => { c with control := none }
    | some a => ⟨some a.next, fun k => applyOp (a.work k) (c.stack k)⟩

def initial (P : Program) (code : List Bool) : Config P :=
  ⟨some P.start, fun k => if k = 0 then code else []⟩

def advance (P : Program) (bits : ℕ → Bool) (c : Config P) : ℕ → Config P
  | 0 => c
  | t + 1 => step P (advance P bits c t) (bits t)

def run (P : Program) (code : List Bool) (bits : ℕ → Bool) (t : ℕ) : Config P :=
  advance P bits (initial P code) t

@[simp] theorem advance_zero (P : Program) (bits : ℕ → Bool) (c : Config P) :
    advance P bits c 0 = c := rfl

theorem advance_front (P : Program) (bits : ℕ → Bool) (c : Config P) (t : ℕ) :
    advance P bits c (t + 1) = advance P (fun j => bits (j + 1)) (step P c (bits 0)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step P (advance P bits c (t + 1)) (bits (t + 1)) =
      step P (advance P (fun j => bits (j + 1)) (step P c (bits 0)) t) (bits (t + 1))
    rw [ih]

theorem advance_add (P : Program) (bits : ℕ → Bool) (c : Config P) (t u : ℕ) :
    advance P bits c (t + u) = advance P (fun j => bits (t + j)) (advance P bits c t) u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change step P (advance P bits c (t + u)) (bits (t + u)) =
      step P (advance P (fun j => bits (t + j)) (advance P bits c t) u) (bits (t + u))
    rw [ih]

theorem advance_halted (P : Program) (bits : ℕ → Bool) (c : Config P)
    (hc : c.control = none) (t : ℕ) : advance P bits c t = c := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [advance, ih, step, hc]

abbrev Control (P : Program) := Fin P.states ⊕ (Fin P.states × (Fin 3 → Option Bool))
noncomputable def controlEquiv (P : Program) : Control P ≃ Fin (Fintype.card (Control P)) :=
  Fintype.equivFin _
noncomputable def normal (P : Program) (q : Fin P.states) : Fin (Fintype.card (Control P)) :=
  controlEquiv P (.inl q)
noncomputable def pending (P : Program) (q : Fin P.states) (w : Fin 3 → Option Bool) :
    Fin (Fintype.card (Control P)) := controlEquiv P (.inr (q, w))

noncomputable def machine (P : Program) : Machine where
  states := Fintype.card (Control P)
  start := normal P P.start
  transition q top bit :=
    match (controlEquiv P).symm q with
    | .inl q => (P.transition q top bit).map fun a =>
        ⟨pending P a.next (fun k => pendingWrite (a.work k)),
          fun k => firstWrite (a.work k) (top k),
          fun k => match a.work k with
            | .keep => .stay
            | .pop => if (top k).isSome then .right else .stay
            | .push _ => .left⟩
    | .inr (q, w) =>
      some ⟨normal P q, fun k => (w k).or (top k), fun _ => .stay⟩

noncomputable def concrete (P : Program) (c : Config P) (h : Fin 3 → ℤ) :
    Configuration (machine P) where
  control := c.control.map (normal P)
  head := h
  tape k := cells (c.stack k) (h k)

@[simp] theorem decode_normal (P : Program) (q : Fin P.states) :
    (controlEquiv P).symm (normal P q) = .inl q := (controlEquiv P).symm_apply_apply _
@[simp] theorem decode_pending (P : Program) (q : Fin P.states) (w : Fin 3 → Option Bool) :
    (controlEquiv P).symm (pending P q w) = .inr (q,w) := (controlEquiv P).symm_apply_apply _

def newHeads {P : Program} (c : Config P) (h : Fin 3 → ℤ) (a : Act P.states) : Fin 3 → ℤ :=
  fun k => h k + (shiftOp (a.work k) (c.stack k)).offset

theorem double_step (P : Program) (c : Config P) (h : Fin 3 → ℤ) (b₁ b₂ : Bool) :
    ∃ h', MeanPayoff.step (machine P)
      (MeanPayoff.step (machine P) (concrete P c h) b₁) b₂ =
        concrete P (step P c b₁) h' := by
  rcases c with ⟨q, xs⟩
  cases q with
  | none => exact ⟨h, rfl⟩
  | some q =>
    let top : Fin 3 → Option Bool := fun k => (xs k).head?
    have ht : (fun k => cells (xs k) (h k) (h k)) = top := by funext k; exact cells_top _ _
    cases ha : P.transition q top b₁ with
    | none =>
      refine ⟨h, ?_⟩
      simp only [MeanPayoff.step, concrete, Option.map_some, machine, decode_normal,
        ht, ha, Option.map_none]
      simp only [top] at ha
      simp only [step]; rw [ha]; rfl
    | some a =>
      refine ⟨newHeads ⟨some q, xs⟩ h a, ?_⟩
      simp only [MeanPayoff.step, concrete, Option.map_some, machine, decode_normal,
        ht, ha, Option.map_some, decode_pending]
      simp only [top] at ha
      simp only [step]; rw [ha]
      apply concrete_ext
      · rfl
      · funext k
        cases he : a.work k <;> cases hx : xs k <;> simp [newHeads, top, he, hx, shiftOp, Direction.offset]
      · funext k
        cases he : a.work k <;> cases hx : xs k <;>
          simpa [newHeads, top, he, hx, shiftOp, Direction.offset] using cells_applyOp (a.work k) (xs k) (h k)

theorem concrete_initial (P : Program) (code : List Bool) :
    MeanPayoff.initial (machine P) code = concrete P (initial P code) (fun _ => 0) := by
  apply concrete_ext
  · rfl
  · rfl
  · funext k j
    by_cases hk : k = 0 <;> simp [MeanPayoff.initial, concrete, initial, cells, hk]

theorem simulate (P : Program) (code : List Bool) (bits : ℕ → Bool) (t : ℕ) :
    ∃ h, MeanPayoff.run (machine P) code bits (2 * t) =
      concrete P (run P code (fun j => bits (2 * j)) t) h := by
  induction t with
  | zero => exact ⟨fun _ => 0, concrete_initial P code⟩
  | succ t ih =>
    obtain ⟨h, hh⟩ := ih
    have he : 2 * (t + 1) = 2 * t + 1 + 1 := by omega
    rw [he, MeanPayoff.run, MeanPayoff.run, hh]
    exact double_step P _ h _ _

@[simp] theorem concrete_halted (P : Program) (c : Config P) (h : Fin 3 → ℤ) :
    (concrete P c h).control = none ↔ c.control = none := by
  change c.control.map (normal P) = none ↔ c.control = none
  exact Option.map_eq_none_iff

end WorkStack
end MeanPayoff
end

end OAI
