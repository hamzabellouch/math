import OAI.Computability.MeanPayoff.FiniteSuccess

namespace OAI

section

namespace MeanPayoff
namespace BinaryStack

inductive Op where
  | keep | pop | push (b : Bool)
  deriving DecidableEq, Fintype

structure Act (q : ℕ) where
  next : Fin q
  work : Fin 2 → Op
  emit : Option Bool

structure Program where
  states : ℕ
  start : Fin states
  transition : Fin states → (Fin 2 → Option Bool) → Bool → Option (Act states)

structure Config (P : Program) where
  control : Option (Fin P.states)
  stack : Fin 2 → List Bool
  output : List Bool

def applyOp : Op → List Bool → List Bool
  | .keep, xs => xs
  | .pop, xs => xs.tail
  | .push b, xs => b :: xs

def shiftOp : Op → List Bool → Direction
  | .keep, _ => .stay
  | .pop, [] => .stay
  | .pop, _ :: _ => .right
  | .push _, _ => .left

def firstWrite : Op → Symbol → Symbol
  | .pop, _ => none
  | _, a => a

def pendingWrite : Op → Option Bool
  | .push b => some b
  | _ => none

def step (P : Program) (c : Config P) (bit : Bool) : Config P :=
  match c.control with
  | none => c
  | some q =>
    match P.transition q (fun k => (c.stack k).head?) bit with
    | none => { c with control := none }
    | some a =>
      ⟨some a.next, fun k => applyOp (a.work k) (c.stack k),
        c.output ++ a.emit.toList⟩

def initial (P : Program) (code : List Bool) : Config P :=
  ⟨some P.start, fun k => if k = 0 then code else [], []⟩

def run (P : Program) (code : List Bool) (random : ℕ → Bool) : ℕ → Config P
  | 0 => initial P code
  | t + 1 => step P (run P code random t) (random t)

def cells (xs : List Bool) (h : ℤ) (j : ℤ) : Symbol :=
  if 0 ≤ j - h then xs[(j - h).toNat]? else none

@[simp] theorem cells_top (xs : List Bool) (h : ℤ) : cells xs h h = xs.head? := by
  cases xs <;> simp [cells]

@[simp] theorem cells_nil (h : ℤ) : cells [] h = fun _ => none := by
  funext j; simp [cells]

theorem cells_push (xs : List Bool) (b : Bool) (h : ℤ) :
    cells (b :: xs) (h - 1) = Function.update (cells xs h) (h - 1) (some b) := by
  funext j
  by_cases he : j = h - 1
  · subst j; simp [cells]
  · rw [Function.update_of_ne he]
    by_cases hj : h ≤ j
    · have hn : (j - (h - 1)).toNat = (j - h).toNat + 1 := by omega
      simp only [cells, show 0 ≤ j - (h - 1) by omega, show 0 ≤ j - h by omega,
        ↓reduceIte, hn, List.getElem?_cons_succ]
    · have hn : j < h - 1 := by omega
      simp only [cells, show ¬0 ≤ j - (h - 1) by omega, show ¬0 ≤ j - h by omega, ↓reduceIte]

theorem cells_pop (xs : List Bool) (b : Bool) (h : ℤ) :
    cells xs (h + 1) = Function.update (cells (b :: xs) h) h none := by
  funext j
  by_cases he : j = h
  · subst j; simp [cells]
  · rw [Function.update_of_ne he]
    by_cases hj : h < j
    · have hn : (j - h).toNat = (j - (h + 1)).toNat + 1 := by omega
      simp only [cells, show 0 ≤ j - (h + 1) by omega, show 0 ≤ j - h by omega,
        ↓reduceIte, hn, List.getElem?_cons_succ]
    · simp only [cells, show ¬0 ≤ j - (h + 1) by omega, show ¬0 ≤ j - h by omega, ↓reduceIte]

theorem cells_emit (xs : List Bool) (b : Bool) :
    cells (xs ++ [b]) 0 = Function.update (cells xs 0) (xs.length : ℤ) (some b) := by
  funext j
  by_cases he : j = xs.length
  · subst j; simp [cells]
  · rw [Function.update_of_ne he]
    by_cases hj : 0 ≤ j
    · simp only [cells, sub_zero, hj, ↓reduceIte]
      by_cases hk : j.toNat < xs.length
      · rw [List.getElem?_append_left hk]
      · have hg : xs.length < j.toNat := by omega
        simp only [List.getElem?_eq_none (by omega : xs.length ≤ j.toNat),
          List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega :
            (xs ++ [b]).length ≤ j.toNat)]
    · simp only [cells, sub_zero, hj, ↓reduceIte]

abbrev Control (P : Program) := Fin P.states ⊕ (Fin P.states × (Fin 2 → Option Bool))

noncomputable def controlEquiv (P : Program) : Control P ≃ Fin (Fintype.card (Control P)) :=
  Fintype.equivFin _

noncomputable def normal (P : Program) (q : Fin P.states) : Fin (Fintype.card (Control P)) :=
  controlEquiv P (.inl q)

noncomputable def pending (P : Program) (q : Fin P.states) (w : Fin 2 → Option Bool) :
    Fin (Fintype.card (Control P)) := controlEquiv P (.inr (q, w))

noncomputable def machine (P : Program) : Machine where
  states := Fintype.card (Control P)
  start := normal P P.start
  transition q top bit :=
    match (controlEquiv P).symm q with
    | .inl q =>
      (P.transition q (fun k => top ⟨k.val, by omega⟩) bit).map fun a =>
        ⟨pending P a.next (fun k => pendingWrite (a.work k)),
          fun k => if hk : k.val < 2 then firstWrite (a.work ⟨k.val, hk⟩) (top k)
            else a.emit,
          fun k => if hk : k.val < 2 then
            match a.work ⟨k.val, hk⟩ with
            | .keep => .stay
            | .pop => if (top k).isSome then .right else .stay
            | .push _ => .left
          else if a.emit.isSome then .right else .stay⟩
    | .inr (q, w) =>
      some ⟨normal P q, fun k => if hk : k.val < 2 then
          (w ⟨k.val, hk⟩).or (top k) else top k,
        fun _ => .stay⟩

noncomputable def concrete (P : Program) (c : Config P) (h : Fin 2 → ℤ) : Configuration (machine P) where
  control := c.control.map (normal P)
  head k := if hk : k.val < 2 then h ⟨k.val, hk⟩ else c.output.length
  tape k := if hk : k.val < 2 then cells (c.stack ⟨k.val, hk⟩) (h ⟨k.val, hk⟩)
    else cells c.output 0

@[simp] theorem cells_end (xs : List Bool) : cells xs 0 (xs.length : ℤ) = none := by
  simp [cells]

theorem cells_applyOp (op : Op) (xs : List Bool) (h : ℤ) :
    let h' := h + (shiftOp op xs).offset
    let t := Function.update (cells xs h) h (firstWrite op xs.head?)
    Function.update t h' ((pendingWrite op).or (t h')) =
      cells (applyOp op xs) h' := by
  cases op with
  | keep => simp [shiftOp, Direction.offset, firstWrite, pendingWrite, applyOp]
  | pop =>
    cases xs with
    | nil => simp [shiftOp, Direction.offset, firstWrite, pendingWrite, applyOp]
    | cons b xs =>
      simp only [shiftOp, Direction.offset, firstWrite, pendingWrite, Option.none_or,
        Function.update_eq_self, applyOp, List.tail_cons]
      exact (cells_pop xs b h).symm
  | push b =>
    simp only [shiftOp, Direction.offset, firstWrite, pendingWrite,
      ← cells_top xs h, Function.update_eq_self, Option.some_or, applyOp]
    simpa only [sub_eq_add_neg] using (cells_push xs b h).symm

def newHeads {P : Program} (c : Config P) (h : Fin 2 → ℤ) (a : Act P.states) : Fin 2 → ℤ :=
  fun k => h k + (shiftOp (a.work k) (c.stack k)).offset

@[ext] theorem concrete_ext {M : Machine} {a b : Configuration M}
    (hc : a.control = b.control) (hh : a.head = b.head) (ht : a.tape = b.tape) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem decode_normal (P : Program) (q : Fin P.states) :
    (controlEquiv P).symm (normal P q) = .inl q := by
  exact (controlEquiv P).symm_apply_apply _
@[simp] theorem decode_pending (P : Program) (q : Fin P.states) (w : Fin 2 → Option Bool) :
    (controlEquiv P).symm (pending P q w) = .inr (q,w) := by
  exact (controlEquiv P).symm_apply_apply _

@[simp] theorem shiftOp_formula (op : Op) (xs : List Bool) :
    (match op with
     | .keep => Direction.stay
     | .pop => if xs = [] then Direction.stay else Direction.right
     | .push _ => Direction.left) = shiftOp op xs := by
  cases op <;> cases xs <;> rfl

theorem double_step (P : Program) (c : Config P) (h : Fin 2 → ℤ) (b₁ b₂ : Bool) :
    ∃ h', MeanPayoff.step (machine P)
      (MeanPayoff.step (machine P) (concrete P c h) b₁) b₂ =
        concrete P (step P c b₁) h' := by
  rcases c with ⟨q, xs, out⟩
  cases q with
  | none => exact ⟨h, rfl⟩
  | some q =>
    let top : Fin 2 → Option Bool := fun k => (xs k).head?
    cases ha : P.transition q top b₁ with
    | none =>
      refine ⟨h, ?_⟩
      simp only [MeanPayoff.step, concrete, Option.map_some, machine, decode_normal]
      have ht : (fun k : Fin 2 =>
          (if hk : k.val < 2 then cells (xs ⟨k.val, hk⟩) (h ⟨k.val, hk⟩)
            else cells out 0)
          (if hk : k.val < 2 then h ⟨k.val, hk⟩ else out.length)) = top := by
        funext k
        simp only [Fin.isLt, ↓reduceDIte, Fin.eta, cells_top, top]
      simp only [ht, ha, Option.map_none]
      simp only [top] at ha
      simp only [step]
      rw [ha]
      rfl
    | some a =>
      refine ⟨newHeads ⟨some q, xs, out⟩ h a, ?_⟩

      simp only [MeanPayoff.step, concrete, Option.map_some, machine, decode_normal]
      have ht : (fun k : Fin 2 =>
          (if hk : k.val < 2 then cells (xs ⟨k.val, hk⟩) (h ⟨k.val, hk⟩)
            else cells out 0)
          (if hk : k.val < 2 then h ⟨k.val, hk⟩ else out.length)) = top := by
        funext k
        simp only [Fin.isLt, ↓reduceDIte, Fin.eta, cells_top, top]
      simp only [ht, ha, Option.map_some, decode_pending]
      simp only [top] at ha
      simp only [step]
      rw [ha]
      apply concrete_ext
      · rfl
      · funext k
        fin_cases k
        · simp [newHeads, Direction.offset]
        · simp [newHeads, Direction.offset]
        · cases he : a.emit <;> simp [Direction.offset, he]
      · funext k
        fin_cases k
        · simpa [newHeads] using cells_applyOp (a.work 0) (xs 0) (h 0)
        · simpa [newHeads] using cells_applyOp (a.work 1) (xs 1) (h 1)
        · cases he : a.emit with
          | none =>
            have hu : Function.update (cells out 0) (out.length : ℤ) none = cells out 0 := by
              simpa only [cells_end] using Function.update_eq_self (out.length : ℤ) (cells out 0)
            simp [he, hu]
          | some b => simpa [newHeads, he] using (cells_emit out b).symm

theorem concrete_initial (P : Program) (code : List Bool) :
    MeanPayoff.initial (machine P) code = concrete P (initial P code) (fun _ => 0) := by
  apply concrete_ext
  · rfl
  · funext k; fin_cases k <;> rfl
  · funext k j
    fin_cases k
    · simp [MeanPayoff.initial, concrete, initial, cells]
    · simp [MeanPayoff.initial, concrete, initial, cells]
    · simp [MeanPayoff.initial, concrete, initial]

theorem simulate (P : Program) (code : List Bool) (bits : ℕ → Bool) (t : ℕ) :
    ∃ h, MeanPayoff.run (machine P) code bits (2 * t) =
      concrete P (run P code (fun j => bits (2 * j)) t) h := by
  induction t with
  | zero => exact ⟨fun _ => 0, concrete_initial P code⟩
  | succ t ih =>
    obtain ⟨h, hh⟩ := ih
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega, MeanPayoff.run, MeanPayoff.run, hh]
    obtain ⟨h', he⟩ := double_step P (run P code (fun j => bits (2 * j)) t) h
      (bits (2 * t)) (bits (2 * t + 1))
    exact ⟨h', he⟩

@[simp] theorem concrete_halted (P : Program) (c : Config P) (h : Fin 2 → ℤ) :
    (concrete P c h).control = none ↔ c.control = none := by
  change c.control.map (normal P) = none ↔ c.control = none
  exact Option.map_eq_none_iff

theorem concrete_output (P : Program) (c : Config P) (h : Fin 2 → ℤ) (j : ℤ) :
    (concrete P c h).tape 2 j = cells c.output 0 j := rfl

theorem cells_ofFn (n : ℕ) (f : Fin n → Bool) (v : Fin n) :
    cells (List.ofFn f) 0 (v.val : ℤ) = some (f v) := by
  simp [cells]

theorem cells_outside (xs : List Bool) (j : ℤ)
    (hj : j < 0 ∨ (xs.length : ℤ) ≤ j) : cells xs 0 j = none := by
  rcases hj with hj | hj
  · simp [cells, show ¬0 ≤ j by omega]
  · simp [cells, show 0 ≤ j by omega, List.getElem?_eq_none (by omega : xs.length ≤ j.toNat)]

theorem concrete_correct (P : Program) (c : Config P) (h : Fin 2 → ℤ)
    (G : Game) (out : Fin G.n → Bool) (hh : c.control = none)
    (hc : c.output = List.ofFn out) (ho : CorrectSet G out) :
    CorrectOutput G (concrete P c h) := by
  refine ⟨(concrete_halted P c h).2 hh, ?_, ?_, ?_⟩
  · intro v
    simpa only [concrete_output, hc, cells_ofFn, Option.some.injEq] using ho v
  · intro v
    simp only [concrete_output, hc, cells_ofFn, Option.some.injEq]
    rw [← ho v]
    cases out v <;> simp
  · intro j hj
    rw [concrete_output, hc]
    apply cells_outside
    simpa only [List.length_ofFn] using hj

end BinaryStack
end MeanPayoff
end

end OAI
