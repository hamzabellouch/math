import OAI.Computability.WLIdentification.WordCommands

namespace OAI

namespace WLIdentification

namespace BoundedWords
open StackModel (Command)

/-- Word-register programs with bounded, captured-count loops. No unbounded
natural register, whole-input transition or host-language oracle is available. -/
inductive Program (K : Type) where
  | skip
  | clear (k : K)
  | push (k : K) (b : Bool)
  | pop (k : K)
  | copy (a b : K)
  | seq (p q : Program K)
  | cases (k : K) (empty zero one : Program K)
  | repeat (k : K) (body : Program K)

namespace Program
variable {K : Type} [DecidableEq K]

def eval : Program K → (K → Word) → (K → Word)
  | .skip, S => S
  | .clear k, S => Function.update S k []
  | .push k b, S => Function.update S k (S k ++ [b])
  | .pop k, S => Function.update S k (S k).dropLast
  | .copy a b, S => Function.update S b (S a)
  | .seq p q, S => q.eval (p.eval S)
  | .cases k nil zero one, S => match (S k).getLast? with
      | none => nil.eval S
      | some false => zero.eval S
      | some true => one.eval S
  | .repeat k p, S => p.eval^[(S k).length] S

def Size (S : K → Word) (B : ℕ) : Prop := ∀ k, (S k).length ≤ B

/-- An explicit bound on all data consumed by an execution. Proving this
invariant for an algorithm, rather than assuming its runtime, yields a cost. -/
def Fits : Program K → (K → Word) → ℕ → Prop
  | .skip, S, B | .clear _, S, B | .push _ _, S, B | .pop _, S, B | .copy _ _, S, B => Size S B
  | .seq p q, S, B => p.Fits S B ∧ q.Fits (p.eval S) B
  | .cases k nil zero one, S, B => Size S B ∧ match (S k).getLast? with
      | none => nil.Fits S B
      | some false => zero.Fits S B
      | some true => one.Fits S B
  | .repeat k p, S, B => Size S B ∧ ∀ i < (S k).length, p.Fits (p.eval^[i] S) B

abbrev Work : Program K → Type
  | .skip | .clear _ | .push _ _ | .pop _ => Empty
  | .copy _ _ => Unit
  | .seq p q => Work p ⊕ Work q
  | .cases _ p q r => Work p ⊕ (Work q ⊕ Work r)
  | .repeat _ p => Work p ⊕ Bool

noncomputable instance workFintype (p : Program K) : Fintype p.Work := by
  induction p <;> simp only [Work] <;> infer_instance
instance workDecidableEq : (p : Program K) → DecidableEq p.Work
  | .skip | .clear _ | .push _ _ | .pop _ => inferInstance
  | .copy _ _ => inferInstance
  | .seq p q => @instDecidableEqSum _ _ (workDecidableEq p) (workDecidableEq q)
  | .cases _ p q r => @instDecidableEqSum _ _ (workDecidableEq p)
      (@instDecidableEqSum _ _ (workDecidableEq q) (workDecidableEq r))
  | .repeat _ p => @instDecidableEqSum _ _ (workDecidableEq p) inferInstance

def cost : Program K → ℕ → ℕ
  | .skip, _ => 1
  | .clear _, B => 3 * B + 2
  | .push _ _, _ | .pop _, _ => 2
  | .copy _ _, B => 12 * B + 8
  | .seq p q, B => p.cost B + q.cost B
  | .cases _ p q r, B => max (p.cost B) (max (q.cost B) (r.cost B)) + 4
  | .repeat _ p, B => 12 * B + 8 + (p.cost B + 2) * B + 2

noncomputable def compile : (p : Program K) → Command (K ⊕ p.Work) (Option Bool)
  | .skip => .modify (fun _ => none)
  | .clear k => Command.clear (.inl k)
  | .push k b => .seq (.push (.inl k) (fun _ => b)) (.modify (fun _ => none))
  | .pop k => .seq (.pop (.inl k) (fun _ _ => none)) (.modify (fun _ => none))
  | .copy a b => if a = b then .modify (fun _ => none)
      else Command.copy (.inl a) (.inl b) (.inr ())
  | .seq p q => .seq (p.compile.rename Command.embedLeft) (q.compile.rename Command.embedRight)
  | .cases k p q r =>
      .seq (Command.read (.inl k)) (.branch Option.isSome
        (.seq (Command.emit (.inl k)) (.branch (fun b => b.getD false)
          (r.compile.rename (Command.embedRight.trans Command.embedRight))
          (q.compile.rename (Command.embedLeft.trans Command.embedRight))))
        (p.compile.rename Command.embedLeft))
  | .repeat k p => .seq (Command.copy (.inl k) (.inr (.inr false)) (.inr (.inr true)))
      (Command.drain (.inr (.inr false)) (p.compile.rename Command.embedLeft))

omit [DecidableEq K] in
/-- Every syntactic cost is polynomial in the maintained word bound; its
constants depend on finite code, not the input or loop counts. -/
theorem cost_polynomial (p : Program K) : ∃ C d : ℕ, ∀ B, p.cost B ≤ C * (B + 1)^d := by
  induction p with
  | skip => exact ⟨1, 0, by intro B; simp [cost]⟩
  | clear k => exact ⟨5, 1, by intro B; simp only [cost, pow_one]; omega⟩
  | push k b | pop k => exact ⟨2, 0, by intro B; simp [cost]⟩
  | copy a b => exact ⟨20, 1, by intro B; simp only [cost, pow_one]; omega⟩
  | seq p q ihp ihq =>
    obtain ⟨C, d, hp⟩ := ihp
    obtain ⟨D, e, hq⟩ := ihq
    refine ⟨C + D, max d e, ?_⟩
    intro B
    have hp' := (hp B).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) (le_max_left d e)))
    have hq' := (hq B).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by omega) (le_max_right d e)))
    dsimp only [cost]
    nlinarith
  | cases k p q r ihp ihq ihr =>
    obtain ⟨C,d,hp⟩ := ihp
    obtain ⟨D,e,hq⟩ := ihq
    obtain ⟨E,f,hr⟩ := ihr
    let z := max d (max e f)
    have hdz : d ≤ z := le_max_left _ _
    have hez : e ≤ z := (le_max_left _ _).trans (le_max_right _ _)
    have hfz : f ≤ z := (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨C + D + E + 4, z, ?_⟩
    intro B
    have hpos : 1 ≤ (B+1)^z := Nat.one_le_pow _ _ (by omega)
    have hp' := (hp B).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) hdz))
    have hq' := (hq B).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by omega) hez))
    have hr' := (hr B).trans (Nat.mul_le_mul_left E (Nat.pow_le_pow_right (by omega) hfz))
    dsimp only [cost]
    have hm : max (p.cost B) (max (q.cost B) (r.cost B)) ≤ (C+D+E)*(B+1)^z := by
      apply max_le
      · nlinarith
      · apply max_le <;> nlinarith
    nlinarith
  | «repeat» k p ih =>
    obtain ⟨C,d,hp⟩ := ih
    refine ⟨C+24, d+1, ?_⟩
    intro B
    have hpos : 1 ≤ (B+1)^d := Nat.one_le_pow _ _ (by omega)
    have hmul := Nat.mul_le_mul_right B (hp B)
    simp only [cost, pow_succ]
    nlinarith

end Program
end BoundedWords

namespace BoundedWords.Program
open StackModel.Command
variable {K : Type} [DecidableEq K]

@[simp] theorem elim_empty {A B : Type} :
    Sum.elim (fun _ : A => ([] : Word)) (fun _ : B => []) = fun _ => [] := by
  funext x; cases x <;> rfl

theorem update_inl {A : Type} [DecidableEq A] (S : K → Word) (W : A → Word) (k : K) (v : Word) :
    Function.update (Sum.elim S W) (.inl k) v = Sum.elim (Function.update S k v) W := by
  funext x
  cases x with
  | inl j => by_cases h : j = k <;> simp [h]
  | inr a => simp

def Correct (p : Program K) : Prop := ∀ S B, p.Fits S B → ∀ s : Option Bool,
  ∃ n ≤ p.cost B, Exec p.compile s (Sum.elim S (fun _ => [])) none
    (Sum.elim (p.eval S) (fun _ => [])) n

theorem correct_skip : Correct (.skip : Program K) := by
  intro S B h s
  exact ⟨1, le_rfl, .modify _ _ _⟩

theorem correct_clear (k : K) : Correct (.clear k) := by
  intro S B h s
  obtain ⟨n, hn, he⟩ := clear_exec (.inl k : K ⊕ Empty) s (Sum.elim S (fun _ => []))
  refine ⟨n, hn.trans (by dsimp only [Sum.elim_inl, cost]; have := h k; omega), ?_⟩
  simpa only [compile, eval, update_inl] using he

theorem correct_push (k : K) (b : Bool) : Correct (.push k b) := by
  intro S B h s
  have he := Exec.seq (Exec.push (.inl k : K ⊕ Empty) (fun _ : Option Bool => b) s
    (Sum.elim S (fun _ => []))) (Exec.modify (fun _ => none) s _)
  refine ⟨2, le_rfl, ?_⟩
  simpa only [compile, eval, Sum.elim_inl, update_inl] using he

theorem correct_pop (k : K) : Correct (.pop k) := by
  intro S B h s
  have he := Exec.seq (Exec.pop (.inl k : K ⊕ Empty) (fun _ _ : Option Bool => none) s
    (Sum.elim S (fun _ => []))) (Exec.modify (fun _ => none) none _)
  refine ⟨2, le_rfl, ?_⟩
  simpa only [compile, eval, Sum.elim_inl, update_inl] using he

theorem correct_copy (a b : K) : Correct (.copy a b) := by
  intro S B h s
  by_cases hab : a = b
  · subst b
    refine ⟨1, by dsimp [cost]; omega, ?_⟩
    simpa only [compile, ite_eq_left rfl, ite_true, eval, Function.update_eq_self] using
      (Exec.modify (fun _ : Option Bool => none) s (Sum.elim S (fun _ : Unit => [])))
  · obtain ⟨n, hn, he⟩ := copy_exec (.inl a : K ⊕ Unit) (.inl b) (.inr ())
      (by simpa using hab) (by simp) (by simp) s (Sum.elim S (fun _ => []))
    have hs : Function.update (Function.update (Sum.elim S (fun _ : Unit => [])) (.inl b) (S a))
        (.inr ()) [] = Sum.elim (Function.update S b (S a)) (fun _ => []) := by
      rw [update_inl]
      exact Function.update_eq_self _ _
    refine ⟨n, hn.trans ?_, ?_⟩
    · simp only [Sum.elim_inl, Sum.elim_inr, List.length_nil, mul_zero, add_zero, cost]
      have := h a; have := h b; omega
    · simpa only [compile, ite_eq_right hab, eval, Sum.elim_inl, hs] using he

theorem correct_seq {p q : Program K} (hp : Correct p) (hq : Correct q) : Correct (.seq p q) := by
  intro S B h s
  obtain ⟨a, ha, hea⟩ := hp S B h.1 s
  obtain ⟨b, hb, heb⟩ := hq (p.eval S) B h.2 none
  refine ⟨b+a, by dsimp only [cost]; omega, ?_⟩
  have he := Exec.seq (hea.left (fun _ : q.Work => [])) (heb.right (fun _ : p.Work => []))
  simpa only [compile, eval, elim_empty] using he

theorem correct_cases {k : K} {p q r : Program K} (hp : Correct p) (hq : Correct q)
    (hr : Correct r) : Correct (.cases k p q r) := by
  intro S B h s
  let W : K ⊕ (p.Work ⊕ (q.Work ⊕ r.Work)) → Word := Sum.elim S (fun _ => [])
  cases hl : (S k).getLast? with
  | none =>
    have hw : S k = [] := List.getLast?_eq_none_iff.mp hl
    obtain ⟨n, hn, he⟩ := hp S B (by simpa only [Fits, hl] using h.2) none
    have hu : Function.update W (.inl k) [] = W := by
      have hw' : W (.inl k) = [] := hw
      rw [← hw']
      exact Function.update_eq_self _ _
    have hread : Exec (StackModel.Command.read (.inl k)) s W none W 1 := by
      simpa only [StackModel.Command.read, show W (.inl k) = [] from hw, List.getLast?_nil, List.dropLast_nil, hu] using
        Exec.pop (.inl k) (fun _ b => b) s W
    have he' := he.left (fun _ : q.Work ⊕ r.Work => [])
    simp only [elim_empty] at he'
    refine ⟨n+2, by dsimp only [cost]; have := le_max_left (p.cost B) (max (q.cost B) (r.cost B)); omega, ?_⟩
    have hex := Exec.seq hread (Exec.branch_false (test := Option.isSome) (c := .seq (emit (.inl k))
      (.branch (fun x : Option Bool => x.getD false)
        (r.compile.rename (embedRight.trans embedRight))
        (q.compile.rename (embedLeft.trans embedRight)))) (by rfl) he')
    simpa only [compile, eval, hl, elim_empty, W, Nat.add_assoc] using hex
  | some b =>
    obtain ⟨v, hv⟩ := List.getLast?_eq_some_iff.mp hl
    let V := Function.update W (.inl k) v
    have hread : Exec (StackModel.Command.read (.inl k)) s W (some b) V 1 := by
      simpa only [StackModel.Command.read, show W (.inl k) = v ++ [b] from hv,
        List.getLast?_append, List.getLast?_singleton, Option.some_or,
        List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, V] using
        Exec.pop (.inl k) (fun _ b => b) s W
    have hrestore : Function.update V (.inl k) (V (.inl k) ++ [b]) = W := by
      simp only [V, Function.update_self, Function.update_idem]
      exact (congrArg (Function.update W (.inl k)) hv.symm).trans (Function.update_eq_self _ _)
    have hemit : Exec (emit (.inl k)) (some b) V (some b) W 1 := by
      simpa only [emit, Option.getD_some, hrestore] using
        Exec.push (.inl k) (fun x : Option Bool => x.getD false) (some b) V
    cases b with
    | false =>
      obtain ⟨n, hn, he⟩ := hq S B (by simpa only [hl] using h.2) (some false)
      have he' := (he.left (fun _ : r.Work => [])).right (fun _ : p.Work => [])
      simp only [elim_empty] at he'
      have hex := Exec.seq hread (Exec.branch_true (test := Option.isSome) (d := p.compile.rename embedLeft) (by rfl)
        (Exec.seq hemit (Exec.branch_false (test := fun x : Option Bool => x.getD false)
          (c := r.compile.rename (embedRight.trans embedRight)) (by rfl) he')))
      refine ⟨n+4, ?_, ?_⟩
      · dsimp only [cost]
        have := (le_max_left (q.cost B) (r.cost B)).trans (le_max_right (p.cost B) _)
        omega
      · simpa only [compile, eval, hl, elim_empty, rename_rename,
          Function.Embedding.coe_trans, W, Nat.add_assoc, Nat.reduceAdd] using hex
    | true =>
      obtain ⟨n, hn, he⟩ := hr S B (by simpa only [hl] using h.2) (some true)
      have he' := (he.right (fun _ : q.Work => [])).right (fun _ : p.Work => [])
      simp only [elim_empty] at he'
      have hex := Exec.seq hread (Exec.branch_true (test := Option.isSome) (d := p.compile.rename embedLeft) (by rfl)
        (Exec.seq hemit (Exec.branch_true (test := fun x : Option Bool => x.getD false)
          (d := q.compile.rename (embedLeft.trans embedRight)) (by rfl) he')))
      refine ⟨n+4, ?_, ?_⟩
      · dsimp only [cost]
        have := (le_max_right (q.cost B) (r.cost B)).trans (le_max_right (p.cost B) _)
        omega
      · simpa only [compile, eval, hl, elim_empty, rename_rename,
          Function.Embedding.coe_trans, W, Nat.add_assoc, Nat.reduceAdd] using hex

end BoundedWords.Program

namespace BoundedWords.Program
open StackModel.Command
variable {K : Type} [DecidableEq K]

def counterData (w : Word) : Bool → Word := fun b => if b then [] else w

def loopState {A : Type} (S : K → Word) (w : Word) : K ⊕ (A ⊕ Bool) → Word :=
  Sum.elim S (Sum.elim (fun _ => []) (counterData w))

omit [DecidableEq K] in
@[simp] theorem loopState_var {A : Type} (S : K → Word) (w : Word) (k : K) :
    loopState (A:=A) S w (.inl k) = S k := rfl
omit [DecidableEq K] in
@[simp] theorem loopState_counter {A : Type} (S : K → Word) (w : Word) :
    loopState (A:=A) S w (.inr (.inr false)) = w := rfl
omit [DecidableEq K] in
@[simp] theorem loopState_temp {A : Type} (S : K → Word) (w : Word) :
    loopState (A:=A) S w (.inr (.inr true)) = [] := rfl

omit [DecidableEq K] in
@[simp] theorem loopState_empty {A : Type} (S : K → Word) :
    loopState (A:=A) S [] = Sum.elim S (fun _ => []) := by
  funext x
  cases x with
  | inl k => rfl
  | inr x => cases x with
    | inl a => rfl
    | inr b => cases b <;> rfl

theorem update_counter {A : Type} [DecidableEq A] (S : K → Word) (w v : Word) :
    Function.update (loopState (A:=A) S w) (.inr (.inr false)) v = loopState S v := by
  funext x
  cases x with
  | inl k => simp [loopState]
  | inr x => cases x with
    | inl a => simp [loopState]
    | inr b => cases b <;> simp [loopState, counterData]

/-- The captured counter is consumed one bit per loop, independently of all
public registers modified by the body. -/
theorem drain_repeat {p : Program K} (hp : Correct p) (B : ℕ) (S : K → Word) (w : Word)
    (hfit : ∀ i < w.length, p.Fits (p.eval^[i] S) B) (s : Option Bool) :
    ∃ n ≤ (p.cost B + 2) * w.length + 2,
      Exec (drain (.inr (.inr false)) (p.compile.rename embedLeft)) s (loopState S w) none
        (loopState (p.eval^[w.length] S) []) n := by
  induction w using List.reverseRecOn generalizing S s with
  | nil =>
    have hr : Exec (StackModel.Command.read (.inr (.inr false))) s
        (loopState (A:=p.Work) S []) none (loopState S []) 1 := by
      simpa only [StackModel.Command.read, loopState_counter, List.getLast?_nil,
        List.dropLast_nil, update_counter] using
        Exec.pop (.inr (.inr false)) (fun _ b => b) s (loopState (A:=p.Work) S [])
    exact ⟨2, by simp, Exec.seq hr (.while_false _ _ _ _ rfl)⟩
  | append_singleton w b ih =>
    obtain ⟨a, ha, hea⟩ := hp S B (hfit 0 (by simp)) (some b)
    have hbody := hea.left (counterData w)
    have htail : ∀ i < w.length, p.Fits (p.eval^[i] (p.eval S)) B := by
      intro i hi
      simpa only [Function.iterate_succ_apply] using hfit (i+1) (by simp; omega)
    obtain ⟨n, hn, hen⟩ := ih (S := p.eval S) htail none
    have hr : Exec (StackModel.Command.read (.inr (.inr false))) s
        (loopState (A:=p.Work) S (w ++ [b])) (some b) (loopState S w) 1 := by
      simpa only [StackModel.Command.read, loopState_counter, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, List.dropLast_append_cons,
        List.dropLast_singleton, List.append_nil, update_counter] using
        Exec.pop (.inr (.inr false)) (fun _ b => b) s (loopState (A:=p.Work) S (w ++ [b]))
    dsimp only [drain] at hen
    cases hen with
    | seq hpop hwhile =>
      cases hpop
      rename_i t
      have hex := Exec.seq hr (Exec.while_true (by rfl)
        (Exec.seq hbody (Exec.pop (.inr (.inr false)) (fun _ b => b) none (loopState (A:=p.Work) (p.eval S) w))) hwhile)
      refine ⟨t + 1 + (a + 1 + 1), ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton] at *
        nlinarith
      · simpa only [drain, List.length_append, List.length_singleton,
          Function.iterate_succ_apply, StackModel.Command.read, loopState, Nat.add_assoc] using hex

theorem correct_repeat {k : K} {p : Program K} (hp : Correct p) : Correct (.repeat k p) := by
  intro S B h s
  obtain ⟨a, ha, hea⟩ := copy_exec (.inl k : K ⊕ (p.Work ⊕ Bool))
    (.inr (.inr false)) (.inr (.inr true)) (by simp) (by simp) (by simp) s (loopState S [])
  have hstate : Function.update
      (Function.update (loopState (A:=p.Work) S []) (.inr (.inr false)) (S k))
      (.inr (.inr true)) [] = loopState S (S k) := by
    rw [update_counter]
    exact Function.update_eq_self _ _
  simp only [loopState_var, hstate] at hea
  obtain ⟨b, hb, heb⟩ := drain_repeat hp B S (S k) h.2 none
  refine ⟨b+a, ?_, ?_⟩
  · have hk := h.1 k
    simp only [loopState_counter, loopState_temp, loopState_var, List.length_nil, mul_zero,
      zero_add, cost] at ha ⊢
    have hm := Nat.mul_le_mul_left (p.cost B+2) hk
    omega
  · simpa only [compile, eval, loopState_empty] using Exec.seq hea heb

/-- Fully uniform compilation, with all work stacks again empty at the boundary. -/
theorem correct (p : Program K) : p.Correct := by
  induction p with
  | skip => exact correct_skip
  | clear k => exact correct_clear k
  | push k b => exact correct_push k b
  | pop k => exact correct_pop k
  | copy a b => exact correct_copy a b
  | seq p q hp hq => exact correct_seq hp hq
  | cases k p q r hp hq hr => exact correct_cases hp hq hr
  | «repeat» k p hp => exact correct_repeat hp

end BoundedWords.Program

end WLIdentification

end OAI
