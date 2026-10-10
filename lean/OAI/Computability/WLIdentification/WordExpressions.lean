import OAI.Computability.WLIdentification.BoundedWords

namespace OAI

namespace WLIdentification

namespace WordExpressions

/-- A finite, first-order word language. Loops capture a word length; their
body sees both a unary iteration index and the previous accumulator. -/
inductive Expr : ℕ → Type where
  | var {n} (i : Fin n) : Expr n
  | nil {n} : Expr n
  | snoc {n} (e : Expr n) (b : Bool) : Expr n
  | drop {n} (e : Expr n) : Expr n
  | cases {n} (e empty zero one : Expr n) : Expr n
  | bind {n} (e : Expr n) (f : Expr (n+1)) : Expr n
  | loop {n} (count init : Expr n) (body : Expr (n+2)) : Expr n

namespace Expr

def stages {n} (f : (Fin (n+2) → Word) → Word) (S : Fin n → Word) (a : Word) : ℕ → Word
  | 0 => a
  | i+1 => f (Fin.snoc (Fin.snoc S (List.replicate i false)) (stages f S a i))

def eval : {n : ℕ} → Expr n → (Fin n → Word) → Word
  | _, .var i, S => S i
  | _, .nil, _ => []
  | _, .snoc e b, S => e.eval S ++ [b]
  | _, .drop e, S => (e.eval S).dropLast
  | _, .cases e p q r, S => match (e.eval S).getLast? with
      | none => p.eval S
      | some false => q.eval S
      | some true => r.eval S
  | _, .bind e f, S => f.eval (Fin.snoc S (e.eval S))
  | _, .loop c a f, S => stages f.eval S (a.eval S) (c.eval S).length

def Bounded : {n : ℕ} → Expr n → (Fin n → Word) → ℕ → Prop
  | _, .var i, S, B => (S i).length ≤ B
  | _, .nil, _, _ => True
  | _, .snoc e b, S, B => e.Bounded S B ∧ (e.eval S ++ [b]).length ≤ B
  | _, .drop e, S, B => e.Bounded S B
  | _, .cases e p q r, S, B => e.Bounded S B ∧ match (e.eval S).getLast? with
      | none => p.Bounded S B
      | some false => q.Bounded S B
      | some true => r.Bounded S B
  | _, .bind e f, S, B => e.Bounded S B ∧ f.Bounded (Fin.snoc S (e.eval S)) B
  | _, .loop c a f, S, B => c.Bounded S B ∧ a.Bounded S B ∧
      ∀ i < (c.eval S).length, f.Bounded (Fin.snoc (Fin.snoc S (List.replicate i false))
        (stages f.eval S (a.eval S) i)) B

theorem length_le {n} (e : Expr n) (S : Fin n → Word) (B : ℕ) (h : e.Bounded S B) :
    (e.eval S).length ≤ B := by
  induction e with
  | var i => exact h
  | nil => exact Nat.zero_le _
  | snoc e b _ => exact h.2
  | drop e ih => exact (by simpa only [eval, List.length_dropLast] using
      (Nat.sub_le _ 1).trans (ih S h))
  | cases e p q r _ hp hq hr =>
    dsimp only [eval]
    cases he : (e.eval S).getLast? with
    | none => exact hp S (by simpa only [Bounded, he] using h.2)
    | some b => cases b with
      | false => exact hq S (by simpa only [Bounded, he] using h.2)
      | true => exact hr S (by simpa only [Bounded, he] using h.2)
  | bind e f _ hf => exact hf _ h.2
  | loop c a f _ ha hf =>
    have hb : ∀ j ≤ (c.eval S).length, (stages f.eval S (a.eval S) j).length ≤ B := by
      intro j hj
      cases j with
      | zero => exact ha S h.2.1
      | succ j => exact hf _ (h.2.2 j (by omega))
    exact hb _ le_rfl

open StackModel.Command

/-- The result register is separate from immutable inputs; all temporary
register numbers are at least `base` and are cleared before return. -/
def code : {n : ℕ} → Expr n → (Fin n → ℕ) → ℕ → ℕ → StackModel.Command ℕ (Option Bool)
  | _, .var i, env, out, base => copy (env i) out base
  | _, .nil, _, out, _ => clear out
  | _, .snoc e b, env, out, base => .seq (e.code env out base) (.push out (fun _ => b))
  | _, .drop e, env, out, base => .seq (e.code env out base) (.pop out (fun _ _ => none))
  | _, .cases e p q r, env, out, base =>
      .seq (e.code env base (base+1))
        (.seq (StackModel.Command.read base)
          (.seq (.branch Option.isSome
             (.branch (fun x => x.getD false) (r.code env out (base+1)) (q.code env out (base+1)))
             (p.code env out (base+1))) (clear base)))
  | _, .bind e f, env, out, base =>
      .seq (e.code env base (base+1))
        (.seq (f.code (Fin.snoc env base) out (base+1)) (clear base))
  | _, .loop c a f, env, out, base =>
      .seq (c.code env base (base+1))
        (.seq (a.code env out (base+1))
          (.seq (drain base
            (.seq (copy out (base+2) (base+3))
              (.seq (f.code (Fin.snoc (Fin.snoc env (base+1)) (base+2)) out (base+3))
                (.seq (clear (base+2)) (.push (base+1) (fun _ => false))))))
            (clear (base+1))))

def cost : {n : ℕ} → Expr n → ℕ → ℕ
  | _, .var _, B => 12*B+8
  | _, .nil, B => 3*B+2
  | _, .snoc e _, B | _, .drop e, B => e.cost B+1
  | _, .cases e p q r, B => e.cost B + max (p.cost B) (max (q.cost B) (r.cost B)) + 3*B+5
  | _, .bind e f, B => e.cost B+f.cost B+3*B+2
  | _, .loop c a f, B => c.cost B+a.cost B+(f.cost B+12*B+13)*B+3*B+4

end Expr
end WordExpressions
namespace StackModel.Command
variable {K : Type} [DecidableEq K]

/-- General indexed captured-count iteration, preserving an arbitrary counter
prefix during each body execution. -/
theorem drain_indexed (body : Command K (Option Bool)) (counter : K)
    (X : ℕ → K → Word) (hX : ∀ i, X i counter = []) (cost start : ℕ) (w : Word)
    (hbody : ∀ i, start ≤ i → i < start+w.length → ∀ v s,
      ∃ t ≤ cost, Exec body s (Function.update (X i) counter v) none
        (Function.update (X (i+1)) counter v) t) (s : Option Bool) :
    ∃ n ≤ (cost+2)*w.length+2,
      Exec (drain counter body) s (Function.update (X start) counter w) none
        (X (start+w.length)) n := by
  induction w using List.reverseRecOn generalizing start s with
  | nil =>
    have hu : Function.update (X start) counter [] = X start := by
      rw [← hX start]; exact Function.update_eq_self _ _
    have hr : Exec (StackModel.Command.read counter) s (X start) none (X start) 1 := by
      simpa only [StackModel.Command.read, hX, List.getLast?_nil, List.dropLast_nil,
        hu] using Exec.pop counter (fun _ b => b) s (X start)
    refine ⟨2, by simp, ?_⟩
    simpa only [drain, List.length_nil, Nat.add_zero, hu] using
      Exec.seq hr (Exec.while_false Option.isSome (.seq body (StackModel.Command.read counter)) none (X start) rfl)
  | append_singleton w b ih =>
    obtain ⟨a, ha, hea⟩ := hbody start le_rfl (by simp) w (some b)
    obtain ⟨n, hn, hen⟩ := ih (start+1) (by
      intro i hi hj v s
      apply hbody i (by omega) (by simp only [List.length_append, List.length_singleton]; omega) v s) none
    have hr : Exec (StackModel.Command.read counter) s
        (Function.update (X start) counter (w++[b])) (some b)
        (Function.update (X start) counter w) 1 := by
      simpa only [StackModel.Command.read, Function.update_self, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, List.dropLast_append_cons,
        List.dropLast_singleton, List.append_nil, Function.update_idem] using
        Exec.pop counter (fun _ b => b) s (Function.update (X start) counter (w++[b]))
    dsimp only [drain] at hen
    cases hen with
    | seq hpop hwhile =>
      cases hpop
      rename_i t
      have hex := Exec.seq hr (Exec.while_true (by rfl)
        (Exec.seq hea (Exec.pop counter (fun _ b => b) none (Function.update (X (start+1)) counter w))) hwhile)
      refine ⟨t+1+(a+1+1), ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton] at *
        nlinarith
      · have hl : start+1+w.length = start+(w++[b]).length := by simp; omega
        simpa only [drain, StackModel.Command.read, hl, Nat.add_assoc] using hex

end StackModel.Command
namespace WordExpressions.Expr
open StackModel.Command

def Clean (S : ℕ → Word) (b : ℕ) : Prop := ∀ i, b ≤ i → S i = []

theorem Clean.mono {S b c} (h : Clean S b) (hbc : b ≤ c) : Clean S c :=
  fun _ hi => h _ (hbc.trans hi)

theorem Clean.update {S b k w} (h : Clean S b) (hk : k < b) : Clean (Function.update S k w) b := by
  intro i hi
  rw [Function.update_of_ne (by omega)]
  exact h i hi

theorem update_clean {S b w} (h : Clean S b) : Clean (Function.update S b w) (b+1) :=
  (h.mono (by omega)).update (by omega)

def Correct {n} (e : Expr n) : Prop :=
  ∀ (B : ℕ) (S : ℕ → Word) (env : Fin n → ℕ) (out base : ℕ),
    out < base → (∀ i, env i < base ∧ env i ≠ out) → Clean S base → (S out).length ≤ B →
    e.Bounded (S ∘ env) B → ∀ s : Option Bool,
      ∃ t ≤ e.cost B, Exec (e.code env out base) s S none
        (Function.update S out (e.eval (S ∘ env))) t

theorem correct_var {n} (i : Fin n) : Correct (.var i) := by
  intro B S env out base ho he hc hb h s
  obtain ⟨t, ht, hex⟩ := copy_exec (env i) out base (he i).2 (by have := (he i).1; omega)
    (by omega) s S
  have htemp := hc base le_rfl
  have hu : Function.update (Function.update S out (S (env i))) base [] =
      Function.update S out (S (env i)) := by
    apply Function.update_eq_self_iff.mpr
    simp only [Function.update_of_ne (by omega : base ≠ out), htemp]
  refine ⟨t, ?_, ?_⟩
  · simp only [htemp, List.length_nil, mul_zero, add_zero] at ht
    exact ht.trans (by dsimp only [cost]; dsimp only [Bounded, Function.comp_apply] at h; omega)
  · simpa only [code, eval, Function.comp_apply, hu] using hex

theorem correct_nil {n} : Correct (.nil : Expr n) := by
  intro B S env out base ho he hc hb _ s
  obtain ⟨t, ht, hex⟩ := clear_exec out s S
  exact ⟨t, ht.trans (by dsimp only [cost]; omega), hex⟩

theorem correct_snoc {n} {e : Expr n} (he : Correct e) (b : Bool) : Correct (.snoc e b) := by
  intro B S env out base ho henv hc hb h s
  obtain ⟨t, ht, hex⟩ := he B S env out base ho henv hc hb h.1 s
  have hx := Exec.seq hex (Exec.push out (fun _ => b) none (Function.update S out (e.eval (S ∘ env))))
  refine ⟨1+t, by dsimp only [cost]; omega, ?_⟩
  simpa only [code, eval, Function.update_self, Function.update_idem] using hx

theorem correct_drop {n} {e : Expr n} (he : Correct e) : Correct (.drop e) := by
  intro B S env out base ho henv hc hb h s
  obtain ⟨t, ht, hex⟩ := he B S env out base ho henv hc hb h s
  have hx := Exec.seq hex (Exec.pop out (fun _ _ => none) none (Function.update S out (e.eval (S ∘ env))))
  refine ⟨1+t, by dsimp only [cost]; omega, ?_⟩
  simpa only [code, eval, Function.update_self, Function.update_idem] using hx

/-- An allocated temporary is invisible to the immutable environment. -/
theorem env_update {n} (S : ℕ → Word) (env : Fin n → ℕ) (base : ℕ) (w : Word)
    (h : ∀ i, env i < base) : Function.update S base w ∘ env = S ∘ env := by
  funext i
  exact Function.update_of_ne (by have := h i; omega) _ _

theorem snoc_env_update {n} (S : ℕ → Word) (env : Fin n → ℕ) (base : ℕ) (w : Word)
    (h : ∀ i, env i < base) : Function.update S base w ∘ Fin.snoc env base = Fin.snoc (S ∘ env) w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [Function.comp_apply, Fin.snoc_castSucc]
    exact Function.update_of_ne (by have := h j; omega) _ _

theorem correct_bind {n} {e : Expr n} {f : Expr (n+1)} (he : Correct e) (hf : Correct f) :
    Correct (.bind e f) := by
  intro B S env out base ho henv hc hb h s
  have hb0 := hc base le_rfl
  obtain ⟨a, ha, hea⟩ := he B S env base (base+1) (by omega)
    (fun i => ⟨by have := (henv i).1; omega, by have := (henv i).1; omega⟩)
    (hc.mono (by omega)) (by simp only [hb0, List.length_nil]; omega) h.1 s
  let v := e.eval (S ∘ env)
  let T := Function.update S base v
  have henv' : ∀ i : Fin (n+1), (Fin.snoc env base : Fin (n+1) → ℕ) i < base+1 ∧ (Fin.snoc env base : Fin (n+1) → ℕ) i ≠ out := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; omega
    · simp only [Fin.snoc_castSucc]; have := henv j; omega
  have henvEq : T ∘ Fin.snoc env base = Fin.snoc (S ∘ env) v :=
    snoc_env_update S env base v (fun i => (henv i).1)
  have hout : T out = S out := Function.update_of_ne (by omega) _ _
  obtain ⟨b, hb', heb⟩ := hf B T (Fin.snoc env base) out (base+1) (by omega) henv'
    (update_clean hc) (hout ▸ hb) (by rw [henvEq]; exact h.2) none
  obtain ⟨c, hc', hec⟩ := clear_exec base none (Function.update T out (f.eval (T ∘ Fin.snoc env base)))
  have hv := e.length_le (S ∘ env) B h.1
  have hlen : (Function.update T out (f.eval (T ∘ Fin.snoc env base)) base).length ≤ B := by
    rw [Function.update_of_ne (by omega)]
    simpa only [T, Function.update_self] using hv
  have hlast : Function.update (Function.update T out (f.eval (T ∘ Fin.snoc env base))) base [] =
      Function.update S out ((Expr.bind e f).eval (S ∘ env)) := by
    rw [Function.update_comm (by omega : out ≠ base), Function.update_idem, ← hb0, Function.update_eq_self]
    rw [henvEq]
    rfl
  refine ⟨c+b+a, ?_, ?_⟩
  · dsimp only [cost]; omega
  · simpa only [code, hlast, Nat.add_assoc] using Exec.seq hea (Exec.seq heb hec)

end WordExpressions.Expr

end WLIdentification

end OAI
