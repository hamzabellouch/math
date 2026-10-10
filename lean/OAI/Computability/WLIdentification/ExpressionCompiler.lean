import OAI.Computability.WLIdentification.WordExpressions

namespace OAI

namespace WLIdentification

namespace WordExpressions.Expr
open StackModel.Command

theorem correct_cases {n} {e p q r : Expr n} (he : Correct e) (hp : Correct p)
    (hq : Correct q) (hr : Correct r) : Correct (.cases e p q r) := by
  intro B S env out base ho henv hc hb h s
  have hb0 := hc base le_rfl
  obtain ⟨a, ha, hea⟩ := he B S env base (base+1) (by omega)
    (fun i => ⟨by have := (henv i).1; omega, by have := (henv i).1; omega⟩)
    (hc.mono (by omega)) (by simp only [hb0, List.length_nil]; omega) h.1 s
  let v := e.eval (S ∘ env)
  let T := Function.update S base v.dropLast
  have hread : Exec (StackModel.Command.read base) none (Function.update S base v)
      v.getLast? T 1 := by
    simpa only [StackModel.Command.read, Function.update_self, Function.update_idem, T] using
      Exec.pop base (fun _ b => b) none (Function.update S base v)
  have henv' : ∀ i, env i < base+1 ∧ env i ≠ out := by
    intro i; have := henv i; omega
  have henvEq : T ∘ env = S ∘ env := env_update S env base _ (fun i => (henv i).1)
  have hout : T out = S out := Function.update_of_ne (by omega) _ _
  have hex : ∃ b ≤ max (p.cost B) (max (q.cost B) (r.cost B))+2,
      Exec (.branch Option.isSome
        (.branch (fun x : Option Bool => x.getD false) (r.code env out (base+1)) (q.code env out (base+1)))
        (p.code env out (base+1))) v.getLast? T none
        (Function.update T out ((Expr.cases e p q r).eval (S ∘ env))) b := by
    cases hv : v.getLast? with
    | none =>
      obtain ⟨b, hb', heb⟩ := hp B T env out (base+1) (by omega) henv' (update_clean hc)
        (hout ▸ hb) (by rw [henvEq]; simpa only [show (e.eval (S ∘ env)).getLast? = none from hv] using h.2) none
      refine ⟨b+1, by have := le_max_left (p.cost B) (max (q.cost B) (r.cost B)); omega, ?_⟩
      simpa only [eval, show (e.eval (S ∘ env)).getLast? = none from hv, henvEq] using
        (Exec.branch_false (c := .branch (fun x : Option Bool => x.getD false)
          (r.code env out (base+1)) (q.code env out (base+1))) (test := Option.isSome) (by rfl) heb)
    | some b => cases b with
      | false =>
        obtain ⟨b, hb', heb⟩ := hq B T env out (base+1) (by omega) henv' (update_clean hc)
          (hout ▸ hb) (by rw [henvEq]; simpa only [show (e.eval (S ∘ env)).getLast? = some false from hv] using h.2) (some false)
        have hh := Exec.branch_true (test := Option.isSome) (d := p.code env out (base+1)) (by rfl)
          (Exec.branch_false (test := fun x : Option Bool => x.getD false) (c := r.code env out (base+1)) (by rfl) heb)
        refine ⟨b+2, ?_, ?_⟩
        · have := (le_max_left (q.cost B) (r.cost B)).trans (le_max_right (p.cost B) _); omega
        · simpa only [eval, show (e.eval (S ∘ env)).getLast? = some false from hv,
            henvEq, Nat.add_assoc, Nat.reduceAdd] using hh
      | true =>
        obtain ⟨b, hb', heb⟩ := hr B T env out (base+1) (by omega) henv' (update_clean hc)
          (hout ▸ hb) (by rw [henvEq]; simpa only [show (e.eval (S ∘ env)).getLast? = some true from hv] using h.2) (some true)
        have hh := Exec.branch_true (test := Option.isSome) (d := p.code env out (base+1)) (by rfl)
          (Exec.branch_true (test := fun x : Option Bool => x.getD false) (d := q.code env out (base+1)) (by rfl) heb)
        refine ⟨b+2, ?_, ?_⟩
        · have := (le_max_right (q.cost B) (r.cost B)).trans (le_max_right (p.cost B) _); omega
        · simpa only [eval, show (e.eval (S ∘ env)).getLast? = some true from hv,
            henvEq, Nat.add_assoc, Nat.reduceAdd] using hh
  obtain ⟨b, hb', heb⟩ := hex
  obtain ⟨c, hc', hec⟩ := clear_exec base none (Function.update T out ((Expr.cases e p q r).eval (S ∘ env)))
  have hv := e.length_le (S ∘ env) B h.1
  have hlen : (Function.update T out ((Expr.cases e p q r).eval (S ∘ env)) base).length ≤ B := by
    rw [Function.update_of_ne (by omega)]
    simp only [T, Function.update_self]
    exact (List.dropLast_sublist v).length_le.trans hv
  have hlast : Function.update (Function.update T out ((Expr.cases e p q r).eval (S ∘ env))) base [] =
      Function.update S out ((Expr.cases e p q r).eval (S ∘ env)) := by
    rw [Function.update_comm (by omega : out ≠ base), Function.update_idem, ← hb0, Function.update_eq_self]
  refine ⟨c+b+1+a, ?_, ?_⟩
  · dsimp only [cost]; omega
  · simpa only [code, hlast, Nat.add_assoc] using Exec.seq hea (Exec.seq hread (Exec.seq heb hec))

end WordExpressions.Expr
namespace WordExpressions.Expr
open StackModel.Command

theorem correct_loop {n} {c a : Expr n} {f : Expr (n+2)} (hcorr : Correct c)
    (haCorr : Correct a) (hf : Correct f) : Correct (.loop c a f) := by
  intro B S env out base ho henv hc hb h s
  let ec := c.eval (S ∘ env)
  let stage := stages f.eval (S ∘ env) (a.eval (S ∘ env))
  have hb0 := hc base le_rfl
  have henvlo : ∀ i, env i < base := fun i => (henv i).1
  have hcB : ec.length ≤ B := c.length_le _ _ h.1
  have hstage : ∀ i ≤ ec.length, (stage i).length ≤ B := by
    intro i hi
    cases i with
    | zero => exact a.length_le _ _ h.2.1
    | succ i => exact f.length_le _ _ (h.2.2 i (by change i < ec.length; omega))
  obtain ⟨u, hu, heu⟩ := hcorr B S env base (base+1) (by omega)
    (fun i => ⟨by have := henvlo i; omega, by have := henvlo i; omega⟩)
    (hc.mono (by omega)) (by simp only [hb0, List.length_nil]; omega) h.1 s
  let S₁ := Function.update S base ec
  have hS₁env : S₁ ∘ env = S ∘ env := env_update S env base ec henvlo
  have hS₁out : S₁ out = S out := Function.update_of_ne (by omega) _ _
  obtain ⟨v, hv, hev⟩ := haCorr B S₁ env out (base+1) (by omega)
    (fun i => ⟨by have := henvlo i; omega, (henv i).2⟩)
    (update_clean hc) (hS₁out ▸ hb) (by rw [hS₁env]; exact h.2.1) none
  let X (i : ℕ) := Function.update (Function.update S out (stage i)) (base+1) (List.replicate i false)
  have hX : ∀ i, X i base = [] := by
    intro i
    simpa only [X, Function.update_of_ne (by omega : base ≠ base+1),
      Function.update_of_ne (by omega : base ≠ out)] using hb0
  let body := StackModel.Command.seq (copy out (base+2) (base+3))
    (.seq (f.code (Fin.snoc (Fin.snoc env (base+1)) (base+2)) out (base+3))
      (.seq (clear (base+2)) (.push (base+1) (fun _ => false))))
  have hbody : ∀ i, 0 ≤ i → i < 0+ec.length → ∀ w s,
      ∃ t ≤ f.cost B+12*B+11, Exec body s (Function.update (X i) base w) none
        (Function.update (X (i+1)) base w) t := by
    intro i _ hi w s
    simp only [zero_add] at hi
    let T := Function.update (X i) base w
    have hTclean : Clean T (base+2) :=
      (((hc.mono (by omega)).update (by omega : out < base+2)).update (by omega : base+1 < base+2)).update (by omega)
    have hTstash := hTclean (base+2) le_rfl
    have hTtmp := hTclean (base+3) (by omega)
    have hTidx : T (base+1) = List.replicate i false := by simp [T, X]
    have hTout : T out = stage i := by
      simp only [T, X, Function.update_of_ne (by omega : out ≠ base),
        Function.update_of_ne (by omega : out ≠ base+1), Function.update_self]
    obtain ⟨u, hu, heu⟩ := copy_exec out (base+2) (base+3) (by omega) (by omega) (by omega) s T
    let W := Function.update T (base+2) (stage i)
    have hcopy : Function.update (Function.update T (base+2) (T out)) (base+3) [] = W := by
      rw [hTout]
      apply Function.update_eq_self_iff.mpr
      simp only [Function.update_of_ne (by omega : base+3 ≠ base+2), hTtmp]
    rw [hcopy] at heu
    have henv' : ∀ j : Fin (n+2),
        (Fin.snoc (Fin.snoc env (base+1)) (base+2) : Fin (n+2) → ℕ) j < base+3 ∧
        (Fin.snoc (Fin.snoc env (base+1)) (base+2) : Fin (n+2) → ℕ) j ≠ out := by
      intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_last]; omega
      · simp only [Fin.snoc_castSucc]
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp only [Fin.snoc_last]; omega
        · simp only [Fin.snoc_castSucc]; have := henv k; omega
    have hWenv : W ∘ Fin.snoc (Fin.snoc env (base+1)) (base+2) =
        Fin.snoc (Fin.snoc (S ∘ env) (List.replicate i false)) (stage i) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [W]
      · simp only [Function.comp_apply, Fin.snoc_castSucc]
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simpa only [Fin.snoc_last, W, Function.update_of_ne (by omega : base+1 ≠ base+2)] using hTidx
        · simp only [Fin.snoc_castSucc, Function.comp_apply, W, T, X,
            Function.update_of_ne (by have := henvlo k; omega : env k ≠ base+2),
            Function.update_of_ne (by have := henvlo k; omega : env k ≠ base),
            Function.update_of_ne (by have := henvlo k; omega : env k ≠ base+1),
            Function.update_of_ne (henv k).2]
    have hWout : W out = stage i := by
      simpa only [W, Function.update_of_ne (by omega : out ≠ base+2)] using hTout
    have hWclean : Clean W (base+3) := (hTclean.mono (by omega)).update (by omega)
    obtain ⟨v, hv, hev⟩ := hf B W (Fin.snoc (Fin.snoc env (base+1)) (base+2)) out (base+3)
      (by omega) henv' hWclean (hWout ▸ hstage i (by omega)) (by rw [hWenv]; exact h.2.2 i hi) none
    have hnext : f.eval (W ∘ Fin.snoc (Fin.snoc env (base+1)) (base+2)) = stage (i+1) := by
      rw [hWenv]; rfl
    rw [hnext] at hev
    obtain ⟨z, hz, hez⟩ := clear_exec (base+2) none (Function.update W out (stage (i+1)))
    have hZlen : (Function.update W out (stage (i+1)) (base+2)).length ≤ B := by
      rw [Function.update_of_ne (by omega)]
      simpa only [W, Function.update_self] using hstage i (by omega)
    let Z := Function.update (Function.update W out (stage (i+1))) (base+2) []
    have hZ : Z = Function.update T out (stage (i+1)) := by
      dsimp only [Z, W]
      rw [Function.update_comm (by omega : out ≠ base+2), Function.update_idem,
        ← hTstash, Function.update_eq_self]
    have hpush := Exec.push (base+1) (fun _ : Option Bool => false) none Z
    have hfinal : Function.update Z (base+1) (Z (base+1) ++ [false]) = Function.update (X (i+1)) base w := by
      rw [hZ]
      funext j
      by_cases hj : j = base
      · subst j; simp only [T, X, Function.update_self, Function.update_of_ne (by omega : base ≠ base+1),
          Function.update_of_ne (by omega : base ≠ out)]
      by_cases hj' : j = base+1
      · subst j
        simp only [Function.update_self, Function.update_of_ne (by omega : base+1 ≠ base),
          Function.update_of_ne (by omega : base+1 ≠ out), hTidx, X]
        exact List.replicate_succ'.symm
      by_cases hj'' : j = out
      · subst j
        simp only [T, X, Function.update_self, Function.update_of_ne hj, Function.update_of_ne hj']
      · simp only [T, X, Function.update_of_ne hj, Function.update_of_ne hj', Function.update_of_ne hj'']
    rw [hfinal] at hpush
    refine ⟨1+z+v+u, ?_, ?_⟩
    · simp only [hTstash, hTtmp, hTout, List.length_nil, mul_zero, zero_add] at hu
      have hs := hstage i (by omega)
      omega
    · simpa only [body, Nat.add_assoc] using Exec.seq heu (Exec.seq hev (Exec.seq hez hpush))
  obtain ⟨w, hw, hew⟩ := drain_indexed body base X hX (f.cost B+12*B+11) 0 ec hbody none
  have hstart : Function.update (X 0) base ec = Function.update S₁ out (a.eval (S₁ ∘ env)) := by
    rw [hS₁env]
    dsimp only [X, stage, stages, List.replicate_zero, S₁]
    rw [Function.update_comm (by omega : out ≠ base+1)]
    have hh := hc (base+1) (by omega)
    rw [← hh, Function.update_eq_self, Function.update_comm (by omega : out ≠ base)]
  rw [hstart] at hew
  simp only [zero_add] at hew
  obtain ⟨z, hz, hez⟩ := clear_exec (base+1) none (X ec.length)
  have hlast : Function.update (X ec.length) (base+1) [] =
      Function.update S out ((Expr.loop c a f).eval (S ∘ env)) := by
    dsimp only [X]
    rw [Function.update_idem, Function.update_comm (by omega : out ≠ base+1)]
    have hh := hc (base+1) (by omega)
    rw [← hh, Function.update_eq_self]
    rfl
  have hlen : (X ec.length (base+1)).length = ec.length := by simp only [X, Function.update_self, List.length_replicate]
  rw [hlen] at hz
  rw [hlast] at hez
  refine ⟨z+w+v+u, ?_, ?_⟩
  · have hm := Nat.mul_le_mul_left (f.cost B+12*B+11+2) hcB
    dsimp only [cost]
    nlinarith
  · simpa only [code, body, Nat.add_assoc] using Exec.seq heu (Exec.seq hev (Exec.seq hew hez))

/-- The finite word language executes on literal stacks, with polynomial cost
in the lengths of all values in its evaluation. -/
theorem correct {n} (e : Expr n) : e.Correct := by
  induction e with
  | var i => exact correct_var i
  | nil => exact correct_nil
  | snoc e b ih => exact correct_snoc ih b
  | drop e ih => exact correct_drop ih
  | cases e p q r he hp hq hr => exact correct_cases he hp hq hr
  | bind e f he hf => exact correct_bind he hf
  | loop c a f hc ha hf => exact correct_loop hc ha hf

end WordExpressions.Expr
namespace StackModel.Command
variable {R : Type}

def registers : Command ℕ R → Finset ℕ
  | .skip | .modify _ => ∅
  | .push k _ | .pop k _ => {k}
  | .seq c d | .branch _ c d => c.registers ∪ d.registers
  | .while _ c => c.registers

def small (c : Command ℕ R) (N : ℕ) : Prop := ∀ k ∈ c.registers, k < N

def finiteIndex (N : ℕ) (h : 0 < N) (k : ℕ) : Fin N := ⟨k % N, Nat.mod_lt _ h⟩

@[simp] theorem finiteIndex_val {N k} (h : 0 < N) (hk : k < N) :
    (finiteIndex N h k).val = k := Nat.mod_eq_of_lt hk

theorem restrict_update {N k} (h : 0 < N) (hk : k < N) (S : ℕ → Word) (v : Word) :
    Function.update S k v ∘ Fin.val = Function.update (S ∘ Fin.val) (finiteIndex N h k) v := by
  funext j
  by_cases hj : j.val = k
  · have he : j = finiteIndex N h k := Fin.ext (hj.trans (finiteIndex_val h hk).symm)
    simp only [Function.comp_apply, hj, Function.update_self]
    rw [he, Function.update_self]
  · have he : j ≠ finiteIndex N h k := by intro he; exact hj (congrArg Fin.val he |>.trans (finiteIndex_val h hk))
    simp only [Function.comp_apply, Function.update_of_ne hj, Function.update_of_ne he]

/-- A syntactically finite register program has the same counted execution on
its finite set of tracks, even though its correctness was proved with convenient
natural register names. -/
theorem Exec.restrict {c : Command ℕ R} {s S t T n} (hex : Exec c s S t T n)
    (N : ℕ) (hN : 0 < N) (hc : c.small N) :
    Exec (c.rename (finiteIndex N hN)) s (S ∘ Fin.val) t (T ∘ Fin.val) n := by
  induction hex with
  | skip s S => exact .skip _ _
  | modify f s S => exact .modify _ _ _
  | push k f s S =>
    have hk := hc k (by simp [registers])
    simpa only [Command.rename, restrict_update hN hk, Function.comp_apply, finiteIndex_val hN hk] using
      Exec.push (finiteIndex N hN k) f s (S ∘ Fin.val)
  | pop k f s S =>
    have hk := hc k (by simp [registers])
    simpa only [Command.rename, restrict_update hN hk, Function.comp_apply, finiteIndex_val hN hk] using
      Exec.pop (finiteIndex N hN k) f s (S ∘ Fin.val)
  | seq _ _ ihc ihd =>
    exact .seq (ihc (fun k hk => hc k (Finset.mem_union_left _ hk)))
      (ihd (fun k hk => hc k (Finset.mem_union_right _ hk)))
  | branch_true ht _ ih => exact .branch_true ht (ih (fun k hk => hc k (Finset.mem_union_left _ hk)))
  | branch_false ht _ ih => exact .branch_false ht (ih (fun k hk => hc k (Finset.mem_union_right _ hk)))
  | while_false test c s S ht => exact .while_false _ _ _ _ ht
  | while_true ht _ _ ihc ihw => exact .while_true ht (ihc hc) (ihw hc)

theorem small_exists (c : Command ℕ R) : ∃ N, 1 < N ∧ c.small N := by
  refine ⟨c.registers.sup id+2, by omega, ?_⟩
  intro k hk
  have h := Finset.le_sup (f := id) hk
  dsimp only [id_eq] at h
  omega

/-- A three-instruction output test after a structured command, followed by a
literal accepting or rejecting stack-machine halt. -/
def testProgram {K : Type} (c : Command K (Option Bool)) (s : Option Bool) (out : K) :
    Program K (Option (Control c) ⊕ (Bool ⊕ Unit)) (Option Bool) where
  main := .inl (some c.entry)
  initialStore := s
  code
    | .inl (some x) => (c.code x).map Sum.inl
    | .inl none => .pop out (fun _ b => b) (.inr (.inr ()))
    | .inr (.inr _) => .branch (fun b => b.getD false) (.inr (.inl true)) (.inr (.inl false))
    | .inr (.inl b) => .halt b

theorem testProgram_embeds {K : Type} (c : Command K (Option Bool)) (s : Option Bool) (out : K) :
    Embeds (c.testProgram s out) c (Sum.inl ∘ some) (.inl none) := by
  intro x
  simp only [testProgram, Function.comp_apply]
  congr 1
  funext a
  cases a <;> rfl

theorem Exec.testRun {K : Type} [DecidableEq K] {c : Command K (Option Bool)} {s S t T n}
    (h : Exec c s S t T n) (input out : K) (w : Word)
    (hS : S = Function.update (fun _ => []) input w) :
    (StackModel.run (c.testProgram s out) input w (3+n)).control =
      .inl ((T out).getLast?.getD false) := by
  have he := h.execution (c.testProgram s out) (Sum.inl ∘ some) (.inl none)
    (c.testProgram_embeds s out)
  subst S
  unfold StackModel.run
  rw [Function.iterate_add_apply]
  change ((StackModel.step (c.testProgram s out))^[3]
    ((StackModel.step (c.testProgram s out))^[n]
      ⟨.inr ((Sum.inl ∘ some) c.entry), s, Function.update (fun _ => []) input w⟩)).control = _
  rw [he]
  change (StackModel.step (c.testProgram s out) (StackModel.step (c.testProgram s out)
    (StackModel.step (c.testProgram s out) ⟨.inr (.inl none), t, T⟩))).control = _
  cases hb : (T out).getLast?.getD false <;> simp [StackModel.step, testProgram, hb]

end StackModel.Command
namespace ComputationBounds

def Polynomial (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ n, f n ≤ C*(n+1)^d

theorem constant (c : ℕ) : Polynomial (fun _ => c) := ⟨c, 0, by simp⟩
theorem identity : Polynomial id := ⟨1, 1, by intro n; simp⟩

theorem add {f g} (hf : Polynomial f) (hg : Polynomial g) : Polynomial (fun n => f n+g n) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C+D, max d e, ?_⟩
  intro n
  have h1 := (hf n).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) (le_max_left d e)))
  have h2 := (hg n).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by omega) (le_max_right d e)))
  nlinarith

theorem mul {f g} (hf : Polynomial f) (hg : Polynomial g) : Polynomial (fun n => f n*g n) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C*D, d+e, ?_⟩
  intro n
  have hh := Nat.mul_le_mul (hf n) (hg n)
  calc
    f n*g n ≤ (C*(n+1)^d)*(D*(n+1)^e) := hh
    _ = (C*D)*(n+1)^(d+e) := by rw [pow_add]; ring

theorem maximum {f g} (hf : Polynomial f) (hg : Polynomial g) : Polynomial (fun n => max (f n) (g n)) := by
  obtain ⟨C,d,h⟩ := add hf hg
  exact ⟨C,d,fun n => (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)).trans (h n)⟩

end ComputationBounds

namespace WordExpressions.Expr
open ComputationBounds

theorem cost_polynomial {n} (e : Expr n) : Polynomial e.cost := by
  induction e with
  | var _ => exact add (mul (constant 12) identity) (constant 8)
  | nil => exact add (mul (constant 3) identity) (constant 2)
  | snoc _ _ ih | drop _ ih => exact add ih (constant 1)
  | cases _ _ _ _ he hp hq hr =>
    exact add (add (add he (maximum hp (maximum hq hr))) (mul (constant 3) identity)) (constant 5)
  | bind _ _ he hf => exact add (add (add he hf) (mul (constant 3) identity)) (constant 2)
  | loop _ _ _ hc ha hf =>
    exact add (add (add (add hc ha) (mul (add (add hf (mul (constant 12) identity)) (constant 13)) identity))
      (mul (constant 3) identity)) (constant 4)

def outputBound {n} (e : Expr n) (B : ℕ) : ℕ :=
  2+(e.cost B+15*B+13)*(2*(B+(e.cost B+15*B+13))+3)

theorem outputBound_polynomial {n} (e : Expr n) : Polynomial e.outputBound := by
  have h := add (add e.cost_polynomial (mul (constant 15) identity)) (constant 13)
  exact add (constant 2) (mul h (add (mul (constant 2) (add identity h)) (constant 3)))

end WordExpressions.Expr

end WLIdentification

end OAI
