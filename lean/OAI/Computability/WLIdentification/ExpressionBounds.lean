import OAI.Computability.WLIdentification.ExpressionCompiler

namespace OAI

namespace WLIdentification

namespace WordExpressions.Expr
open StackModel.Command

def outputCode (e : Expr 1) : StackModel.Command ℕ (Option Bool) :=
  .seq (e.code (fun _ => 0) 1 2) (.seq (clear 0) (.seq (copy 1 0 2) (clear 1)))

theorem outputCode_exec (e : Expr 1) (w : Word) (B : ℕ) (hw : w.length ≤ B)
    (h : e.Bounded (fun _ => w) B) :
    ∃ t ≤ e.cost B+15*B+12, Exec e.outputCode none (Function.update (fun _ => []) 0 w) none
      (Function.update (fun _ => []) 0 (e.eval (fun _ => w))) t := by
  let S : ℕ → Word := Function.update (fun _ => []) 0 w
  have henv : S ∘ (fun _ : Fin 1 => 0) = fun _ => w := by funext i; simp [S]
  have hclean : Clean S 2 := by intro k hk; simp [S, show k ≠ 0 by omega]
  obtain ⟨a, ha, hea⟩ := e.correct B S (fun _ => 0) 1 2 (by omega) (by intro i; omega)
    hclean (by simp [S]) (by rw [henv]; exact h) none
  rw [henv] at hea
  let v := e.eval (fun _ => w)
  have hv : v.length ≤ B := e.length_le _ _ h
  let T := Function.update S 1 v
  obtain ⟨b, hb, heb⟩ := clear_exec 0 none T
  let U := Function.update T 0 []
  obtain ⟨c, hc, hec⟩ := copy_exec 1 0 2 (by omega) (by omega) (by omega) none U
  let V := Function.update (Function.update U 0 (U 1)) 2 []
  obtain ⟨d, hd, hed⟩ := clear_exec 1 none V
  have ht0 : T 0 = w := by simp [T, S]
  have hu0 : U 0 = [] := by simp [U]
  have hu1 : U 1 = v := by simp [U, T]
  have hu2 : U 2 = [] := by simp [U, T, S]
  have hv1 : V 1 = v := by simp [V, U, T]
  have hfinal : Function.update V 1 [] = Function.update (fun _ => []) 0 v := by
    funext k
    by_cases hk0 : k = 0
    · subst k; simp [V, U, T]
    by_cases hk1 : k = 1
    · subst k; simp
    by_cases hk2 : k = 2
    · subst k; simp [V]
    · simp [V, U, T, S, hk0, hk1, hk2]
  rw [hfinal] at hed
  refine ⟨d+c+b+a, ?_, ?_⟩
  · simp only [ht0] at hb
    simp only [hu0, hu1, hu2, List.length_nil, mul_zero, zero_add] at hc
    simp only [hv1] at hd
    omega
  · simpa only [outputCode, Nat.add_assoc] using Exec.seq hea (Exec.seq heb (Exec.seq hec hed))

/-- A complete local, finite-alphabet output producer from a proved bounded
word expression. Uniformity is in the expression, not in its inputs. -/
theorem computes (e : Expr 1) (B : ℕ → ℕ)
    (hw : ∀ n, n ≤ B n) (h : ∀ w, e.Bounded (fun _ => w) (B w.length)) :
    ∃ M : Machine, ComputesWithin M (fun w => e.eval (fun _ => w))
      (fun n => e.outputBound (B n)) := by
  obtain ⟨N,hN,hsmall⟩ := e.outputCode.small_exists
  let c := e.outputCode.rename (finiteIndex N (by omega))
  let input : Fin N := finiteIndex N (by omega) 0
  let P := c.program none
  refine ⟨StackModel.compile P input, ?_⟩
  intro w
  obtain ⟨t,ht,he⟩ := e.outputCode_exec w (B w.length) (hw _) (h w)
  have he' := he.restrict N (by omega) hsmall
  simp only [restrict_update (show 0 < N by omega) (show 0 < N by omega)] at he'
  have hs : (fun _ : ℕ => ([] : Word)) ∘ Fin.val = fun _ : Fin N => [] := rfl
  rw [hs] at he'
  have hr := he'.run input w rfl
  obtain ⟨T,hT,hTe⟩ := StackModel.run_execution P input w (t+1)
  change ∃ T ≤ _, _
  refine ⟨T, ?_, ?_, ?_⟩
  · apply hT.trans
    dsimp only [outputBound]
    have htp : t+1 ≤ e.cost (B w.length)+15*(B w.length)+13 := by omega
    have hn := hw w.length
    gcongr
  · rw [hTe, hr]
    rfl
  · rw [hTe, hr]
    exact StackModel.output_correct P input _ _ rfl

end WordExpressions.Expr

namespace ComputationBounds

theorem compose {f g : ℕ → ℕ} (hf : Polynomial f) (hg : Polynomial g) :
    Polynomial (fun n => f (g n)) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C*(D+1)^d, e*d, ?_⟩
  intro n
  have hn : 1 ≤ (n+1)^e := Nat.one_le_pow _ _ (by omega)
  have hh : g n+1 ≤ (D+1)*(n+1)^e := by have := hg n; nlinarith
  calc
    f (g n) ≤ C*(g n+1)^d := hf _
    _ ≤ C*((D+1)*(n+1)^e)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh _)
    _ = C*(D+1)^d*(n+1)^(e*d) := by rw [mul_pow, ← pow_mul]; ring

theorem dominates {f g : ℕ → ℕ} (hf : Polynomial f) (h : ∀ n, g n ≤ f n) : Polynomial g := by
  obtain ⟨C,d,hf⟩ := hf
  exact ⟨C,d,fun n => (h n).trans (hf n)⟩

end ComputationBounds

namespace WordExpressions.Expr

def liftRen {n m} (r : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.snoc (Fin.castSucc ∘ r) (Fin.last m)

def rename : {n m : ℕ} → (Fin n → Fin m) → Expr n → Expr m
  | _, _, r, .var i => .var (r i)
  | _, _, _, .nil => .nil
  | _, _, r, .snoc e b => .snoc (e.rename r) b
  | _, _, r, .drop e => .drop (e.rename r)
  | _, _, r, .cases e p q s => .cases (e.rename r) (p.rename r) (q.rename r) (s.rename r)
  | _, _, r, .bind e f => .bind (e.rename r) (f.rename (liftRen r))
  | _, _, r, .loop c a f => .loop (c.rename r) (a.rename r) (f.rename (liftRen (liftRen r)))

theorem snoc_liftRen {n m} (r : Fin n → Fin m) (S : Fin m → Word) (a : Word) :
    Fin.snoc S a ∘ liftRen r = Fin.snoc (S ∘ r) a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRen]

theorem stages_rename {n m} (r : Fin n → Fin m)
    (f : (Fin (n+2) → Word) → Word) (g : (Fin (m+2) → Word) → Word)
    (h : ∀ S, g S = f (S ∘ liftRen (liftRen r))) (S : Fin m → Word) (a : Word) (k : ℕ) :
    stages g S a k = stages f (S ∘ r) a k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [stages, h, snoc_liftRen, ih]

@[simp] theorem eval_rename {n m} (e : Expr n) (r : Fin n → Fin m) (S : Fin m → Word) :
    (e.rename r).eval S = e.eval (S ∘ r) := by
  induction e generalizing m with
  | var i | nil => rfl
  | snoc e b ih | drop e ih => simp only [rename, eval, ih]
  | cases e p q s he hp hq hs =>
    simp only [rename, eval, he]
    cases (e.eval (S ∘ r)).getLast? with
    | none => exact hp _ _
    | some b => cases b <;> first | exact hq _ _ | exact hs _ _
  | bind e f he hf => simp only [rename, eval, he, hf, snoc_liftRen]
  | loop c a f hc ha hf =>
    simp only [rename, eval, hc, ha]
    exact stages_rename r _ _ (hf _) _ _ _

@[simp] theorem bounded_rename {n m} (e : Expr n) (r : Fin n → Fin m) (S : Fin m → Word) (B : ℕ) :
    (e.rename r).Bounded S B ↔ e.Bounded (S ∘ r) B := by
  induction e generalizing m with
  | var i | nil => rfl
  | snoc e b ih => simp only [rename, Bounded, ih, eval_rename]
  | drop e ih => exact ih _ _
  | cases e p q s he hp hq hs =>
    simp only [rename, Bounded, he, eval_rename]
    cases (e.eval (S ∘ r)).getLast? with
    | none => rw [hp]
    | some b => cases b <;> simp only [hq, hs]
  | bind e f he hf => simp only [rename, Bounded, he, hf, eval_rename, snoc_liftRen]
  | loop c a f hc ha hf =>
    simp only [rename, Bounded, hc, ha, hf, eval_rename, snoc_liftRen,
      stages_rename r f.eval (f.rename (liftRen (liftRen r))).eval (fun S => eval_rename _ _ S)]

theorem bounded_mono {n} (e : Expr n) {S B D} (h : e.Bounded S B) (hBD : B ≤ D) :
    e.Bounded S D := by
  induction e with
  | var i => exact h.trans hBD
  | nil => trivial
  | snoc e b ih => exact ⟨ih h.1, h.2.trans hBD⟩
  | drop e ih => exact ih h
  | cases e p q r he hp hq hr =>
    refine ⟨he h.1, ?_⟩
    cases hv : (e.eval S).getLast? with
    | none => exact hp (by simpa only [hv] using h.2)
    | some b => cases b with
      | false => exact hq (by simpa only [hv] using h.2)
      | true => exact hr (by simpa only [hv] using h.2)
  | bind e f he hf => exact ⟨he h.1, hf h.2⟩
  | loop c a f hc ha hf => exact ⟨hc h.1, ha h.2.1, fun i hi => hf (h.2.2 i hi)⟩

def liftSub {n m} (s : Fin n → Expr m) : Fin (n+1) → Expr (m+1) :=
  Fin.snoc (fun i => (s i).rename Fin.castSucc) (.var (Fin.last m))

def subst : {n m : ℕ} → (Fin n → Expr m) → Expr n → Expr m
  | _, _, s, .var i => s i
  | _, _, _, .nil => .nil
  | _, _, s, .snoc e b => .snoc (e.subst s) b
  | _, _, s, .drop e => .drop (e.subst s)
  | _, _, s, .cases e p q r => .cases (e.subst s) (p.subst s) (q.subst s) (r.subst s)
  | _, _, s, .bind e f => .bind (e.subst s) (f.subst (liftSub s))
  | _, _, s, .loop c a f => .loop (c.subst s) (a.subst s) (f.subst (liftSub (liftSub s)))

theorem eval_liftSub {n m} (s : Fin n → Expr m) (S : Fin m → Word) (a : Word) :
    (fun i => (liftSub s i).eval (Fin.snoc S a)) = Fin.snoc (fun i => (s i).eval S) a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftSub, eval, Function.comp_def]

theorem stages_subst {n m} (s : Fin n → Expr m)
    (f : (Fin (n+2) → Word) → Word) (g : (Fin (m+2) → Word) → Word)
    (h : ∀ S, g S = f (fun i => (liftSub (liftSub s) i).eval S))
    (S : Fin m → Word) (a : Word) (k : ℕ) :
    stages g S a k = stages f (fun i => (s i).eval S) a k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [stages, h, eval_liftSub, ih]

@[simp] theorem eval_subst {n m} (e : Expr n) (s : Fin n → Expr m) (S : Fin m → Word) :
    (e.subst s).eval S = e.eval (fun i => (s i).eval S) := by
  induction e generalizing m with
  | var i | nil => rfl
  | snoc e b ih | drop e ih => simp only [subst, eval, ih]
  | cases e p q r he hp hq hr =>
    simp only [subst, eval, he]
    cases (e.eval (fun i => (s i).eval S)).getLast? with
    | none => exact hp _ _
    | some b => cases b <;> first | exact hq _ _ | exact hr _ _
  | bind e f he hf => simp only [subst, eval, he, hf, eval_liftSub]
  | loop c a f hc ha hf =>
    simp only [subst, eval, hc, ha]
    exact stages_subst s _ _ (hf _) _ _ _

theorem bounded_liftSub {n m} (s : Fin n → Expr m) (S : Fin m → Word) (a : Word) (B : ℕ)
    (hs : ∀ i, (s i).Bounded S B) (ha : a.length ≤ B) :
    ∀ i, (liftSub s i).Bounded (Fin.snoc S a) B := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [liftSub, Bounded] using ha
  · simpa [liftSub, Function.comp_def] using hs j

theorem bounded_subst {n m} (e : Expr n) (s : Fin n → Expr m) (S : Fin m → Word) (B : ℕ)
    (hs : ∀ i, (s i).Bounded S B) (he : e.Bounded (fun i => (s i).eval S) B) :
    (e.subst s).Bounded S B := by
  induction e generalizing m with
  | var i => exact hs i
  | nil => trivial
  | snoc e b ih => exact ⟨ih _ _ hs he.1, by simpa only [eval_subst] using he.2⟩
  | drop e ih => exact ih _ _ hs he
  | cases e p q r he' hp hq hr =>
    refine ⟨he' _ _ hs he.1, ?_⟩
    simp only [eval_subst]
    cases hv : (e.eval (fun i => (s i).eval S)).getLast? with
    | none => exact hp _ _ hs (by simpa only [hv] using he.2)
    | some b => cases b with
      | false => exact hq _ _ hs (by simpa only [hv] using he.2)
      | true => exact hr _ _ hs (by simpa only [hv] using he.2)
  | bind e f ih hf =>
    refine ⟨ih _ _ hs he.1, ?_⟩
    have hs' := bounded_liftSub s S ((e.subst s).eval S) B hs
      (by rw [eval_subst]; exact e.length_le _ _ he.1)
    apply hf _ _ hs'
    simpa only [eval_liftSub, eval_subst] using he.2
  | loop c a f hc ha hf =>
    refine ⟨hc _ _ hs he.1, ha _ _ hs he.2.1, ?_⟩
    intro i hi
    have hi' : i < (c.eval (fun j => (s j).eval S)).length := by simpa only [eval_subst] using hi
    have hid : i ≤ B := (Nat.le_of_lt hi').trans (c.length_le _ _ he.1)
    have hv : (stages f.eval (fun j => (s j).eval S) (a.eval (fun j => (s j).eval S)) i).length ≤ B := by
      cases i with
      | zero => exact a.length_le _ _ he.2.1
      | succ i => exact f.length_le _ _ (he.2.2 i (by omega))
    have hst := stages_subst s f.eval (f.subst (liftSub (liftSub s))).eval
      (fun S => eval_subst _ _ S) S (a.eval (fun j => (s j).eval S)) i
    simp only [eval_subst] at *
    rw [hst]
    apply hf _ _ (bounded_liftSub _ _ _ _
      (bounded_liftSub _ _ _ _ hs (by simpa using hid)) hv)
    simpa only [eval_liftSub] using he.2.2 i hi'

end WordExpressions.Expr

end WLIdentification

end OAI
