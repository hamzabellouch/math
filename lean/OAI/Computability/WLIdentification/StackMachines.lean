import OAI.Computability.WLIdentification.MachineReduction

namespace OAI

namespace WLIdentification

/- A finite-alphabet parallel-stack interpreter, with local one-tape execution.
All stored registers below range over a fixed finite type; no unbounded value is
hidden in a transition table. The only unbounded data are the literal bit stk. -/
namespace StackModel

inductive Instruction (K Λ R : Type) where
  | push (k : K) (value : R → Bool) (next : Λ)
  | pop (k : K) (store : R → Option Bool → R) (next : Λ)
  | modify (store : R → R) (next : Λ)
  | branch (test : R → Bool) (yes no : Λ)
  | halt (accept : Bool)

structure Program (K Λ R : Type) where
  code : Λ → Instruction K Λ R
  main : Λ
  initialStore : R

structure Config (K Λ R : Type) where
  control : Bool ⊕ Λ
  store : R
  stk : K → List Bool

variable {K Λ R : Type} [DecidableEq K]

def initial (P : Program K Λ R) (input : K) (w : Word) : Config K Λ R :=
  ⟨.inr P.main, P.initialStore, Function.update (fun _ => []) input w⟩

def step (P : Program K Λ R) (c : Config K Λ R) : Config K Λ R :=
  match c.control with
  | .inl _ => c
  | .inr l => match P.code l with
    | .push k value next => ⟨.inr next, c.store,
        Function.update c.stk k (c.stk k ++ [value c.store])⟩
    | .pop k store next => ⟨.inr next, store c.store (c.stk k).getLast?,
        Function.update c.stk k (c.stk k).dropLast⟩
    | .modify store next => ⟨.inr next, store c.store, c.stk⟩
    | .branch test yes no => ⟨.inr (if test c.store then yes else no), c.store, c.stk⟩
    | .halt b => ⟨.inl b, c.store, c.stk⟩

def run (P : Program K Λ R) (input : K) (w : Word) (t : ℕ) : Config K Λ R :=
  (step P)^[t] (initial P input w)

abbrev Alphabet (K : Type) := Option (K → Option Bool)

inductive Phase (K Λ R : Type) where
  | init
  | ready (label : Λ) (store : R)
  | push (stack : K) (label : Λ) (store : R) (value : Bool)
  | pop (stack : K) (label : Λ) (store : Option Bool → R)
  | read (stack : K) (label : Λ) (store : Option Bool → R)
  | back (label : Λ) (store : R)
  deriving Fintype

variable [Fintype K] [Fintype Λ] [Fintype R]

def emptyData : K → Option Bool := fun _ => none

def inputData (input : K) (b : Bool) : K → Option Bool :=
  Function.update emptyData input (some b)

noncomputable def symbol (input : K) (a : Alphabet K) : Fin (Fintype.card (Alphabet K) + 3) := by
  classical
  exact if a = some emptyData then 0 else if a = some (inputData input false) then 1
    else if a = some (inputData input true) then 2 else
      ⟨3 + (Fintype.equivFin (Alphabet K) a).val, by have := (Fintype.equivFin (Alphabet K) a).isLt; omega⟩

noncomputable def decodeSymbol (input : K) (a : Fin (Fintype.card (Alphabet K) + 3)) : Alphabet K :=
  if h0 : a.val = 0 then some emptyData else if h1 : a.val = 1 then some (inputData input false)
  else if h2 : a.val = 2 then some (inputData input true) else
    (Fintype.equivFin (Alphabet K)).symm ⟨a.val - 3, by omega⟩

@[simp] theorem symbol_empty (input : K) : symbol input (some emptyData) = 0 := by
  classical simp [symbol]

@[simp] theorem symbol_input (input : K) (b : Bool) : symbol input (some (inputData input b)) =
    if b then 2 else 1 := by
  classical
  have he : inputData input b ≠ emptyData := by
    intro h
    have := congrFun h input
    simp [inputData, emptyData] at this
  have hne : inputData input true ≠ inputData input false := by
    intro h
    have := congrFun h input
    simp [inputData] at this
  cases b <;> simp [symbol, he, hne]

@[simp] theorem decode_symbol (input : K) (a : Alphabet K) : decodeSymbol input (symbol input a) = a := by
  classical
  unfold symbol
  split_ifs with h0 h1 h2
  · subst a; simp only [decodeSymbol, Fin.val_zero]; norm_num
  · subst a; simp only [decodeSymbol, Fin.val_one]; norm_num
  · subst a; simp only [decodeSymbol, Fin.val_two]; norm_num
  · dsimp [decodeSymbol]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]
    simp

noncomputable def state (p : Phase K Λ R) : Fin (Fintype.card (Phase K Λ R) + 3) :=
  ⟨3 + (Fintype.equivFin (Phase K Λ R) p).val, by have := (Fintype.equivFin (Phase K Λ R) p).isLt; omega⟩

omit [DecidableEq K] in
@[simp] theorem state_ne_one (p : Phase K Λ R) : state p ≠ 1 := by
  intro h; have := congrArg Fin.val h; simp only [state, Fin.val_one] at this; omega
omit [DecidableEq K] in
@[simp] theorem state_ne_two (p : Phase K Λ R) : state p ≠ 2 := by
  intro h; have := congrArg Fin.val h; simp only [state, Fin.val_two] at this; omega

noncomputable def dispatch (P : Program K Λ R) (input : K) (p : Phase K Λ R)
    (a : Fin (Fintype.card (Alphabet K) + 3)) :
    Fin (Fintype.card (Phase K Λ R) + 3) × Fin (Fintype.card (Alphabet K) + 3) × Move :=
  match p with
  | .init => (state (.ready P.main P.initialStore), symbol input none, .right)
  | .ready label s => match P.code label with
    | .push k value next => (state (.push k next s (value s)), a, .stay)
    | .pop k store next => (state (.pop k next (store s)), a, .stay)
    | .modify store next => (state (.ready next (store s)), a, .stay)
    | .branch test yes no => (state (.ready (if test s then yes else no) s), a, .stay)
    | .halt b => (if b then 1 else 2, a, .stay)
  | .push k next s value => match decodeSymbol input a with
    | none => (state p, a, .stay)
    | some d => if (d k).isSome then (state p, a, .right) else
        (state (.back next s), symbol input (some (Function.update d k (some value))), .left)
  | .pop k next store => match decodeSymbol input a with
    | none => (state p, a, .stay)
    | some d => if (d k).isSome then (state p, a, .right) else
        (state (.read k next store), a, .left)
  | .read k next store => match decodeSymbol input a with
    | none => (state (.ready next (store none)), a, .right)
    | some d => (state (.back next (store (d k))), symbol input (some (Function.update d k none)), .left)
  | .back next s => match decodeSymbol input a with
    | none => (state (.ready next s), a, .right)
    | some _ => (state p, a, .left)

/-- A concrete finite local table, using only the three frozen I/O codes and
finitely many fixed extra symbols and states. -/
noncomputable abbrev compile (P : Program K Λ R) (input : K) : Machine where
  extraSymbols := Fintype.card (Alphabet K)
  extraStates := Fintype.card (Phase K Λ R)
  transition q a := if q.val = 0 then (state .init, a, .left) else
    if h : 3 ≤ q.val then
      dispatch P input ((Fintype.equivFin (Phase K Λ R)).symm ⟨q.val - 3, by omega⟩) a
    else (q, a, .stay)

@[simp] theorem transition_state (P : Program K Λ R) (input : K) (p : Phase K Λ R)
    (a : Fin (Fintype.card (Alphabet K) + 3)) :
    (compile P input).transition (state p) a = dispatch P input p a := by
  simp [compile, state]

def column (S : K → Word) (n : ℕ) : K → Option Bool := fun k => (S k)[n]?

noncomputable def tape (input : K) (S : K → Word) (z : ℤ) : Fin (Fintype.card (Alphabet K) + 3) :=
  if z = -1 then symbol input none else
    symbol input (some (if 0 ≤ z then column S z.toNat else emptyData))

@[simp] theorem tape_marker (input : K) (S : K → Word) : tape input S (-1) = symbol input none := by
  simp [tape]

@[simp] theorem tape_nat (input : K) (S : K → Word) (n : ℕ) :
    tape input S n = symbol input (some (column S n)) := by
  simp [tape]

noncomputable def config (P : Program K Λ R) (input : K) (p : Phase K Λ R) (z : ℤ)
    (S : K → Word) : Configuration (compile P input) := ⟨state p, z, tape input S⟩

end StackModel

namespace StackModel
variable {K Λ R : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R]
    (P : Program K Λ R) (input : K)

/-- Literal one-transition equation for every interpreter phase. -/
theorem step_config (p : Phase K Λ R) (z : ℤ) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input p z S) =
      let t := dispatch P input p (tape input S z)
      ⟨t.1, z + t.2.2.displacement, Function.update (tape input S) z t.2.1⟩ := by
  have hn : ¬ ((config P input p z S).state = 1 ∨ (config P input p z S).state = 2) :=
    not_or_intro (state_ne_one p) (state_ne_two p)
  rw [WLIdentification.step, ite_eq_right hn]
  change (let t := (compile P input).transition (state p) (tape input S z)
    ; Configuration.mk (M := compile P input) t.1 (z + t.2.2.displacement)
      (Function.update (tape input S) z t.2.1)) = _
  rw [transition_state]

theorem step_readonly (p q : Phase K Λ R) (z : ℤ) (S : K → Word) (m : Move)
    (h : dispatch P input p (tape input S z) = (state q, tape input S z, m)) :
    WLIdentification.step (compile P input) (config P input p z S) =
      config P input q (z + m.displacement) S := by
  rw [step_config, h]
  change Configuration.mk (M := compile P input) (state q) (z + m.displacement)
    (Function.update (tape input S) z (tape input S z)) = _
  congr 1
  exact Function.update_eq_self z (tape input S)

theorem step_back_nat (label : Λ) (s : R) (S : K → Word) (n : ℕ) :
    WLIdentification.step (compile P input) (config P input (.back label s) n S) =
      config P input (.back label s) ((n : ℤ) - 1) S := by
  simpa only [Move.displacement, sub_eq_add_neg] using
    step_readonly P input (.back label s) (.back label s) n S .left
      (by simp only [tape_nat, dispatch, decode_symbol])

theorem step_back_marker (label : Λ) (s : R) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input (.back label s) (-1) S) =
      config P input (.ready label s) 0 S := by
  simpa only [Move.displacement, neg_add_cancel] using
    step_readonly P input (.back label s) (.ready label s) (-1) S .right
      (by simp only [tape_marker, dispatch, decode_symbol])

theorem back_to_marker (label : Λ) (s : R) (S : K → Word) (n : ℕ) :
    (WLIdentification.step (compile P input))^[n]
      (config P input (.back label s) ((n : ℤ) - 1) S) =
        config P input (.back label s) (-1) S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have he : ((n + 1 : ℕ) : ℤ) - 1 = n := by omega
    rw [he, step_back_nat, ih]

theorem back_to_ready (label : Λ) (s : R) (S : K → Word) (n : ℕ) :
    (WLIdentification.step (compile P input))^[n + 1]
      (config P input (.back label s) ((n : ℤ) - 1) S) =
        config P input (.ready label s) 0 S := by
  rw [Function.iterate_succ_apply', back_to_marker, step_back_marker]

/-- No random access is used: a full rightward scan costs one transition per cell. -/
theorem scan_push (k : K) (label : Λ) (s : R) (b : Bool) (S : K → Word)
    (n : ℕ) (hn : n ≤ (S k).length) :
    (WLIdentification.step (compile P input))^[n]
      (config P input (.push k label s b) 0 S) =
        config P input (.push k label s b) n S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hsome : ((column S n) k).isSome = true := by simp [column]; omega
    have hstep := step_readonly P input (.push k label s b) (.push k label s b) n S .right
      (by simp only [tape_nat, dispatch, decode_symbol, hsome, ite_true])
    simpa only [Move.displacement, Nat.cast_add, Nat.cast_one] using hstep

theorem scan_pop (k : K) (label : Λ) (f : Option Bool → R) (S : K → Word)
    (n : ℕ) (hn : n ≤ (S k).length) :
    (WLIdentification.step (compile P input))^[n]
      (config P input (.pop k label f) 0 S) =
        config P input (.pop k label f) n S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hsome : ((column S n) k).isSome = true := by simp [column]; omega
    have hstep := step_readonly P input (.pop k label f) (.pop k label f) n S .right
      (by simp only [tape_nat, dispatch, decode_symbol, hsome, ite_true])
    simpa only [Move.displacement, Nat.cast_add, Nat.cast_one] using hstep

/-- Erasing the end of a stack, like pushing, only edits one physical cell. -/
theorem tape_push (S : K → Word) (k : K) (b : Bool) :
    tape input (Function.update S k (S k ++ [b])) =
      Function.update (tape input S) ((S k).length : ℤ)
        (symbol input (some (Function.update (column S (S k).length) k (some b)))) := by
  funext z
  by_cases hz : z = ((S k).length : ℤ)
  · subst z
    rw [Function.update_self, tape_nat]
    congr 2
    funext j
    by_cases hj : j = k
    · subst j; simp [column]
    · simp [column, Function.update_of_ne hj]
  · rw [Function.update_of_ne hz]
    unfold tape
    split_ifs with hm hpos
    · rfl
    · congr 2
      funext j
      by_cases hj : j = k
      · subst j
        simp only [column, Function.update_self]
        rw [List.getElem?_append]
        split_ifs with hi
        · rfl
        · have hgt : (S k).length < z.toNat := by omega
          have hn : 1 ≤ z.toNat - (S k).length := by omega
          rw [List.getElem?_eq_none (by simpa using hn), List.getElem?_eq_none (by omega)]
      · simp [column, Function.update_of_ne hj]
    · rfl

end StackModel

end WLIdentification

end OAI
