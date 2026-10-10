import OAI.Computability.WLIdentification.StackMachines

namespace OAI

namespace WLIdentification

namespace StackModel
variable {K Λ R : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R]
    (P : Program K Λ R) (input : K)

theorem push_at_end (k : K) (label : Λ) (s : R) (b : Bool) (S : K → Word) :
    WLIdentification.step (compile P input)
      (config P input (.push k label s b) (S k).length S) =
    config P input (.back label s) (((S k).length : ℤ) - 1)
      (Function.update S k (S k ++ [b])) := by
  rw [step_config]
  have hn : column S (S k).length k = none := by simp [column]
  simp only [tape_nat, dispatch, decode_symbol, hn, Option.isSome_none, Bool.false_eq_true,
    ite_false, Move.displacement]
  unfold config
  congr 1
  exact (tape_push input S k b).symm

theorem push_execution (k : K) (label : Λ) (s : R) (b : Bool) (S : K → Word) :
    (WLIdentification.step (compile P input))^[2 * (S k).length + 2]
      (config P input (.push k label s b) 0 S) =
    config P input (.ready label s) 0 (Function.update S k (S k ++ [b])) := by
  have he : 2 * (S k).length + 2 = ((S k).length + 1) + 1 + (S k).length := by omega
  rw [he, Function.iterate_add_apply, scan_push P input _ _ _ _ _ _ (by omega),
    Function.iterate_add_apply, Function.iterate_one, push_at_end, back_to_ready]

theorem ready_push (l : Λ) (s : R) (k : K) (value : R → Bool) (next : Λ)
    (h : P.code l = .push k value next) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input (.ready l s) 0 S) =
      config P input (.push k next s (value s)) 0 S := by
  have he := step_readonly P input (.ready l s) (.push k next s (value s)) 0 S .stay
    (by simp only [dispatch, h])
  exact he

theorem ready_push_execution (l : Λ) (s : R) (k : K) (value : R → Bool) (next : Λ)
    (h : P.code l = .push k value next) (S : K → Word) :
    (WLIdentification.step (compile P input))^[2 * (S k).length + 3]
      (config P input (.ready l s) 0 S) =
    config P input (.ready next s) 0 (Function.update S k (S k ++ [value s])) := by
  rw [show 2 * (S k).length + 3 = (2 * (S k).length + 2) + 1 by omega,
    Function.iterate_add_apply, Function.iterate_one, ready_push P input _ _ _ _ _ h,
    push_execution]

theorem pop_at_end (k : K) (label : Λ) (f : Option Bool → R) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input (.pop k label f) (S k).length S) =
      config P input (.read k label f) (((S k).length : ℤ) - 1) S := by
  have hn : column S (S k).length k = none := by simp [column]
  simpa only [Move.displacement, sub_eq_add_neg] using
    step_readonly P input (.pop k label f) (.read k label f) (S k).length S .left
      (by simp only [tape_nat, dispatch, decode_symbol, hn, Option.isSome_none,
        Bool.false_eq_true, ite_false])

theorem read_empty (k : K) (label : Λ) (f : Option Bool → R) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input (.read k label f) (-1) S) =
      config P input (.ready label (f none)) 0 S := by
  simpa only [Move.displacement, neg_add_cancel] using
    step_readonly P input (.read k label f) (.ready label (f none)) (-1) S .right
      (by simp only [tape_marker, dispatch, decode_symbol])

theorem tape_pop (S : K → Word) (k : K) (l : Word) (b : Bool) (h : S k = l ++ [b]) :
    tape input (Function.update S k l) =
      Function.update (tape input S) (l.length : ℤ)
        (symbol input (some (Function.update (column S l.length) k none))) := by
  let S' := Function.update S k l
  have he : Function.update S' k (S' k ++ [b]) = S := by
    funext j
    by_cases hj : j = k
    · subst j; simp [S', h]
    · simp [S', hj]
  have ht := tape_push input S' k b
  rw [he, show (S' k).length = l.length by simp [S']] at ht
  have hc : Function.update (column S l.length) k none = column S' l.length := by
    funext j
    by_cases hj : j = k
    · subst j; simp [column, S']
    · simp [column, S', hj]
  rw [hc, ← tape_nat input S' l.length, ht, Function.update_idem, Function.update_eq_self]

theorem read_last (k : K) (label : Λ) (f : Option Bool → R) (S : K → Word)
    (l : Word) (b : Bool) (h : S k = l ++ [b]) :
    WLIdentification.step (compile P input) (config P input (.read k label f) l.length S) =
      config P input (.back label (f (some b))) ((l.length : ℤ) - 1)
        (Function.update S k l) := by
  rw [step_config]
  have hc : column S l.length k = some b := by simp [column, h]
  simp only [tape_nat, dispatch, decode_symbol, hc, Move.displacement]
  unfold config
  congr 1
  exact (tape_pop input S k l b h).symm

theorem pop_execution (k : K) (label : Λ) (f : Option Bool → R) (S : K → Word) :
    (WLIdentification.step (compile P input))^[2 * (S k).length + 2]
      (config P input (.pop k label f) 0 S) =
    config P input (.ready label (f (S k).getLast?)) 0
      (Function.update S k (S k).dropLast) := by
  by_cases he : S k = []
  · have hs : Function.update S k (S k).dropLast = S := by
      rw [he, List.dropLast_nil, ← he, Function.update_eq_self]
    simp only [he, List.length_nil, mul_zero, zero_add, List.getLast?_nil]
    rw [show 2 = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
    have hh := pop_at_end P input k label f S
    simp only [he, List.length_nil, Nat.cast_zero, zero_sub] at hh
    rw [hh, read_empty]
    rw [← he, hs]
  · let l := (S k).dropLast
    let b := (S k).getLast he
    have hs : S k = l ++ [b] := (List.dropLast_append_getLast he).symm
    have hlen : (S k).length = l.length + 1 := by rw [hs]; simp
    have heq : 2 * (S k).length + 2 = (l.length + 1) + 1 + 1 + (S k).length := by omega
    rw [heq, Function.iterate_add_apply, scan_pop P input _ _ _ _ _ (by omega),
      Function.iterate_add_apply, Function.iterate_one, pop_at_end,
      show ((S k).length : ℤ) - 1 = l.length by omega,
      Function.iterate_add_apply, Function.iterate_one, read_last P input k label f S l b hs,
      back_to_ready]
    have hg : (S k).getLast? = some b := List.getLast?_eq_some_getLast he
    rw [hg]

theorem ready_pop (l : Λ) (s : R) (k : K) (store : R → Option Bool → R) (next : Λ)
    (h : P.code l = .pop k store next) (S : K → Word) :
    WLIdentification.step (compile P input) (config P input (.ready l s) 0 S) =
      config P input (.pop k next (store s)) 0 S :=
  step_readonly P input (.ready l s) (.pop k next (store s)) 0 S .stay
    (by simp only [dispatch, h])

theorem ready_pop_execution (l : Λ) (s : R) (k : K) (store : R → Option Bool → R) (next : Λ)
    (h : P.code l = .pop k store next) (S : K → Word) :
    (WLIdentification.step (compile P input))^[2 * (S k).length + 3]
      (config P input (.ready l s) 0 S) =
    config P input (.ready next (store s (S k).getLast?)) 0
      (Function.update S k (S k).dropLast) := by
  rw [show 2 * (S k).length + 3 = (2 * (S k).length + 2) + 1 by omega,
    Function.iterate_add_apply, Function.iterate_one, ready_pop P input _ _ _ _ _ h,
    pop_execution]

end StackModel

namespace StackModel
variable {K Λ R : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R]
    (P : Program K Λ R) (input : K)

noncomputable def encodeConfig (c : Config K Λ R) : Configuration (compile P input) where
  state := match c.control with
    | .inl b => if b then 1 else 2
    | .inr l => state (.ready l c.store)
  head := 0
  tape := tape input c.stk

theorem initial_tape (w : Word) :
    tape input (Function.update (fun _ => []) input w) =
      Function.update (WLIdentification.initial (compile P input) w).tape (-1) (symbol input none) := by
  funext z
  by_cases hz : z = -1
  · subst z; simp
  · rw [Function.update_of_ne hz]
    unfold tape
    rw [ite_eq_right hz]
    change symbol input (some (if 0 ≤ z then column _ z.toNat else emptyData)) =
      if 0 ≤ z then (w[z.toNat]?).elim 0 (inputSymbol (compile P input)) else 0
    split_ifs with hpos
    · have hc : column (Function.update (fun _ => []) input w) z.toNat =
          match w[z.toNat]? with
          | some b => inputData input b
          | none => emptyData := by
        funext k
        by_cases hk : k = input
        · subst k; cases he : w[z.toNat]? <;> simp [column, he, inputData, emptyData]
        · cases w[z.toNat]? <;> simp [column, inputData, emptyData, hk]
      rw [hc]
      cases h : w[z.toNat]? with
      | none => exact symbol_empty input
      | some b => exact symbol_input input b
    · exact symbol_empty input

theorem initial_execution (w : Word) :
    WLIdentification.run (compile P input) w 2 = encodeConfig P input (initial P input w) := by
  let c := WLIdentification.initial (compile P input) w
  have hs : WLIdentification.step (compile P input) c =
      (⟨state .init, -1, c.tape⟩ : Configuration (compile P input)) := by
    unfold WLIdentification.step
    have hn : ¬ (c.state = 1 ∨ c.state = 2) := by
      change ¬ ((0 : Fin (Fintype.card (Phase K Λ R) + 3)) = 1 ∨ 0 = 2)
      simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      omega
    rw [ite_eq_right hn]
    change (⟨state .init, (0 : ℤ) + -1, Function.update c.tape 0 (c.tape 0)⟩ :
      Configuration (compile P input)) = _
    congr 1
    exact Function.update_eq_self 0 c.tape
  have hs' : WLIdentification.step (compile P input)
      (⟨state .init, -1, c.tape⟩ : Configuration (compile P input)) =
      encodeConfig P input (initial P input w) := by
    unfold WLIdentification.step
    dsimp only
    rw [ite_eq_right (not_or_intro (state_ne_one .init) (state_ne_two .init))]
    change (let t := (compile P input).transition (state (.init : Phase K Λ R)) (c.tape (-1))
      ; Configuration.mk (M := compile P input) t.1 (-1 + t.2.2.displacement)
        (Function.update c.tape (-1) t.2.1)) = _
    rw [transition_state]
    dsimp only [dispatch, Move.displacement]
    change (⟨state (.ready P.main P.initialStore), 0,
      Function.update c.tape (-1) (symbol input none)⟩ : Configuration (compile P input)) = _
    unfold encodeConfig initial
    dsimp only
    congr 1
    exact (initial_tape P input w).symm
  change WLIdentification.step (compile P input) (WLIdentification.step (compile P input) c) = _
  rw [hs, hs']

/-- Uniform interpreter cost for one instruction, including all scans. -/
theorem instruction_execution (c : Config K Λ R) (n : ℕ)
    (hn : ∀ k, (c.stk k).length ≤ n) :
    ∃ t ≤ 2 * n + 3, (WLIdentification.step (compile P input))^[t]
      (encodeConfig P input c) = encodeConfig P input (step P c) := by
  obtain ⟨control, s, S⟩ := c
  cases control with
  | inl b => exact ⟨0, by omega, rfl⟩
  | inr l =>
    cases h : P.code l with
    | push k value next =>
      refine ⟨2 * (S k).length + 3, by have := hn k; dsimp at this; omega, ?_⟩
      simpa only [step, h, encodeConfig, config] using ready_push_execution P input l s k value next h S
    | pop k store next =>
      refine ⟨2 * (S k).length + 3, by have := hn k; dsimp at this; omega, ?_⟩
      simpa only [step, h, encodeConfig, config] using ready_pop_execution P input l s k store next h S
    | modify store next =>
      refine ⟨1, by omega, ?_⟩
      have he := step_readonly P input (.ready l s) (.ready next (store s)) 0 S .stay
        (by simp only [dispatch, h])
      simpa only [step, h, encodeConfig, config, Function.iterate_one, Move.displacement, zero_add] using he
    | branch test yes no =>
      refine ⟨1, by omega, ?_⟩
      have he := step_readonly P input (.ready l s) (.ready (if test s then yes else no) s) 0 S .stay
        (by simp only [dispatch, h])
      simpa only [step, h, encodeConfig, config, Function.iterate_one, Move.displacement, zero_add] using he
    | halt b =>
      refine ⟨1, by omega, ?_⟩
      change WLIdentification.step (compile P input) (config P input (.ready l s) 0 S) = _
      rw [step_config]
      simp only [dispatch, h, Move.displacement, add_zero]
      change (⟨(if b then 1 else 2), 0, Function.update (tape input S) 0 (tape input S 0)⟩ :
        Configuration (compile P input)) = _
      simp only [encodeConfig, step, h]
      congr 1
      exact Function.update_eq_self 0 (tape input S)

omit [Fintype K] [Fintype Λ] [Fintype R] in
theorem step_length (c : Config K Λ R) (n : ℕ) (hn : ∀ k, (c.stk k).length ≤ n) :
    ∀ k, ((step P c).stk k).length ≤ n + 1 := by
  intro k
  obtain ⟨control, s, S⟩ := c
  dsimp only at hn
  cases control with
  | inl b => exact (hn k).trans (Nat.le_succ n)
  | inr l =>
    cases h : P.code l <;> simp only [step, h]
    case push j value next =>
      by_cases hk : k = j
      · subst k; simp only [Function.update_self, List.length_append, List.length_singleton]; exact Nat.add_le_add_right (hn j) 1
      · rw [Function.update_of_ne hk]; exact (hn k).trans (Nat.le_succ n)
    case pop j store next =>
      by_cases hk : k = j
      · subst k; simp only [Function.update_self, List.length_dropLast]; have := hn j; omega
      · rw [Function.update_of_ne hk]; exact (hn k).trans (Nat.le_succ n)
    all_goals exact (hn k).trans (Nat.le_succ n)

omit [Fintype K] [Fintype Λ] [Fintype R] in
theorem run_length (w : Word) (t : ℕ) : ∀ k, ((run P input w t).stk k).length ≤ w.length + t := by
  induction t with
  | zero =>
    intro k
    by_cases hk : k = input
    · subst k; simp [run, initial]
    · simp [run, initial, hk]
  | succ t ih =>
    simpa only [run, Function.iterate_succ_apply', Nat.add_assoc] using
      step_length P (run P input w t) (w.length + t) ih

/-- The compilation preserves a real execution with a quadratic simulation bound. -/
theorem run_execution (w : Word) (t : ℕ) :
    ∃ T ≤ 2 + t * (2 * (w.length + t) + 3),
      WLIdentification.run (compile P input) w T = encodeConfig P input (run P input w t) := by
  induction t with
  | zero => exact ⟨2, by omega, initial_execution P input w⟩
  | succ t ih =>
    obtain ⟨T, hT, he⟩ := ih
    obtain ⟨s, hs, he'⟩ := instruction_execution P input (run P input w t)
      (w.length + t) (run_length P input w t)
    refine ⟨s + T, by nlinarith, ?_⟩
    unfold WLIdentification.run at he ⊢
    rw [Function.iterate_add_apply, he, he']
    simp only [run, Function.iterate_succ_apply']

/-- Only the input track is present at output; the fixed marker is at negative position. -/
theorem output_correct (c : Config K Λ R) (w : Word)
    (h : c.stk = Function.update (fun _ => []) input w) :
    Output (encodeConfig P input c) w := by
  constructor
  · intro i
    change tape input c.stk (i.val : ℤ) = _
    rw [h, initial_tape P input w, Function.update_of_ne (by omega)]
    simp only [WLIdentification.initial, Nat.cast_nonneg, ite_true, Int.toNat_natCast,
      List.getElem?_eq_getElem i.isLt, Option.elim_some]
    rfl
  · change tape input c.stk (w.length : ℤ) = 0
    rw [h, initial_tape P input w, Function.update_of_ne (by omega)]
    simp [WLIdentification.initial]

end StackModel

end WLIdentification

end OAI
