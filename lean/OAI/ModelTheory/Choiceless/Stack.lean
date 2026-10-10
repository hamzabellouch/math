import OAI.ModelTheory.Choiceless.Gaussian

namespace OAI

namespace CPTSeparation.StackLang

section

open Turing StateTransition

variable {K : Type} {Γ : K → Type} {σ : Type}

structure Store (Γ : K → Type) (σ : Type) where
  control : σ
  stk : ∀ k, List (Γ k)

inductive Action (Γ : K → Type) (σ : Type) where
  | done
  | push (k : K) (value : σ → Γ k) (next : Action Γ σ)
  | peek (k : K) (update : σ → Option (Γ k) → σ) (next : Action Γ σ)
  | pop (k : K) (update : σ → Option (Γ k) → σ) (next : Action Γ σ)
  | load (update : σ → σ) (next : Action Γ σ)
  | branch (test : σ → Bool) (yes no : Action Γ σ)

namespace Action

variable [DecidableEq K]

def run : Action Γ σ → Store Γ σ → Store Γ σ
  | .done, s => s
  | .push k f a, s => run a ⟨s.control, Function.update s.stk k (f s.control :: s.stk k)⟩
  | .peek k f a, s => run a ⟨f s.control (s.stk k).head?, s.stk⟩
  | .pop k f a, s => run a ⟨f s.control (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | .load f a, s => run a ⟨f s.control, s.stk⟩
  | .branch f a b, s => if f s.control then run a s else run b s

def stmt {Λ : Type} (exit : TM2.Stmt Γ Λ σ) : Action Γ σ → TM2.Stmt Γ Λ σ
  | .done => exit
  | .push k f a => .push k f (stmt exit a)
  | .peek k f a => .peek k f (stmt exit a)
  | .pop k f a => .pop k f (stmt exit a)
  | .load f a => .load f (stmt exit a)
  | .branch f a b => .branch f (stmt exit a) (stmt exit b)

lemma stmt_run {Λ : Type} (exit : TM2.Stmt Γ Λ σ) (a : Action Γ σ) (s : Store Γ σ) :
    TM2.stepAux (a.stmt exit) s.control s.stk =
      TM2.stepAux exit (a.run s).control (a.run s).stk := by
  induction a generalizing s with
  | done => rfl
  | push k f a ih => exact ih ⟨s.control, Function.update s.stk k (f s.control :: s.stk k)⟩
  | peek k f a ih => exact ih ⟨f s.control (s.stk k).head?, s.stk⟩
  | pop k f a ih => exact ih ⟨f s.control (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | load f a ih => exact ih ⟨f s.control, s.stk⟩
  | branch f a b iha ihb =>
      cases hf : f s.control <;> simp [stmt, run, TM2.stepAux, hf, iha, ihb]

end Action

inductive Program (Γ : K → Type) (σ : Type) where
  | atom (a : Action Γ σ)
  | seq (a b : Program Γ σ)
  | cond (test : σ → Bool) (a b : Program Γ σ)
  | loop (test : σ → Bool) (body : Program Γ σ)

inductive Exec [DecidableEq K] : Program Γ σ → Store Γ σ → ℕ → Store Γ σ → Type
  | atom (a) (s) : Exec (.atom a) s 1 (a.run s)
  | seq {a b s t u n m} : Exec a s n t → Exec b t m u → Exec (.seq a b) s (1+(n+m)) u
  | cond_true {f a b s t n} : f s.control = true → Exec a s n t → Exec (.cond f a b) s (1+n) t
  | cond_false {f a b s t n} : f s.control = false → Exec b s n t → Exec (.cond f a b) s (1+n) t
  | loop_false {f body s} : f s.control = false → Exec (.loop f body) s 1 s
  | loop_true {f body s t u n m} : f s.control = true → Exec body s n t → Exec (.loop f body) t m u →
      Exec (.loop f body) s (1+(n+m)) u

namespace Program

def Labels : Program Γ σ → Type
  | .atom _ => Unit
  | .seq a b => Unit ⊕ (Labels a ⊕ Labels b)
  | .cond _ a b => Unit ⊕ (Labels a ⊕ Labels b)
  | .loop _ a => Unit ⊕ Labels a

noncomputable instance finiteLabels (p : Program Γ σ) : Fintype p.Labels := by
  induction p with
  | atom a => change Fintype Unit; infer_instance
  | seq a b iha ihb => change Fintype (Unit ⊕ (a.Labels ⊕ b.Labels)); letI := iha; letI := ihb; infer_instance
  | cond f a b iha ihb => change Fintype (Unit ⊕ (a.Labels ⊕ b.Labels)); letI := iha; letI := ihb; infer_instance
  | loop f a ih => change Fintype (Unit ⊕ a.Labels); letI := ih; infer_instance

def start : (p : Program Γ σ) → p.Labels
  | .atom _ => ()
  | .seq _ _ => .inl ()
  | .cond _ _ _ => .inl ()
  | .loop _ _ => .inl ()

def jump {Λ : Type} : Option Λ → TM2.Stmt Γ Λ σ
  | none => .halt
  | some l => .goto (fun _ => l)

@[simp] lemma stepAux_jump [DecidableEq K] {Λ : Type} (l : Option Λ) (v : σ) (s : ∀ k, List (Γ k)) :
    TM2.stepAux (jump l) v s = ⟨l,v,s⟩ := by cases l <;> rfl

def code {Λ : Type} : (p : Program Γ σ) → (p.Labels → Λ) → Option Λ → p.Labels → TM2.Stmt Γ Λ σ
  | .atom a, _, exit, _ => a.stmt (jump exit)
  | .seq a _, embed, _, .inl _ => .goto (fun _ => embed (.inr (.inl a.start)))
  | .seq a b, embed, _, .inr (.inl l) =>
      code a (fun x => embed (.inr (.inl x))) (some (embed (.inr (.inr b.start)))) l
  | .seq _ b, embed, exit, .inr (.inr l) =>
      code b (fun x => embed (.inr (.inr x))) exit l
  | .cond f a b, embed, _, .inl _ => .branch f
      (.goto (fun _ => embed (.inr (.inl a.start)))) (.goto (fun _ => embed (.inr (.inr b.start))))
  | .cond _ a _, embed, exit, .inr (.inl l) =>
      code a (fun x => embed (.inr (.inl x))) exit l
  | .cond _ _ b, embed, exit, .inr (.inr l) =>
      code b (fun x => embed (.inr (.inr x))) exit l
  | .loop f a, embed, exit, .inl _ => .branch f
      (.goto (fun _ => embed (.inr a.start))) (jump exit)
  | .loop _ a, embed, _, .inr l =>
      code a (fun x => embed (.inr x)) (some (embed (.inl ()))) l

end Program

variable [DecidableEq K]

def configuration {Λ : Type} (label : Option Λ) (s : Store Γ σ) : TM2.Cfg Γ Λ σ :=
  ⟨label,s.control,s.stk⟩

def one_step {Λ : Type} {M : Λ → TM2.Stmt Γ Λ σ} {s t : TM2.Cfg Γ Λ σ}
    (h : TM2.step M s = some t) : EvalsToInTime (TM2.step M) s (some t) 1 := ⟨⟨1,h⟩,le_rfl⟩

noncomputable def Exec.simulates {p : Program Γ σ} {s t : Store Γ σ} {n : ℕ} (h : Exec p s n t)
    {Λ : Type} (M : Λ → TM2.Stmt Γ Λ σ) (embed : p.Labels → Λ) (exit : Option Λ)
    (hc : ∀ l, M (embed l) = p.code embed exit l) :
    EvalsToInTime (TM2.step M) (configuration (some (embed p.start)) s) (some (configuration exit t)) n := by
  induction h generalizing Λ with
  | atom a s =>
      apply one_step
      simp only [configuration, TM2.step, hc, Program.code, Action.stmt_run, Program.stepAux_jump]
  | @seq a b s t u n m ha hb iha ihb =>
      have h₀ : TM2.step M (configuration (some (embed (Program.seq a b).start)) s) =
          some (configuration (some (embed (.inr (.inl a.start)))) s) := by
        simp only [configuration, TM2.step]; rw [hc]; simp [Program.start, Program.code]
      have h₁ := iha M (fun x => embed (.inr (.inl x))) (some (embed (.inr (.inr b.start))))
        (fun l => hc (.inr (.inl l)))
      have h₂ := ihb M (fun x => embed (.inr (.inr x))) exit (fun l => hc (.inr (.inr l)))
      simpa only [Nat.add_comm] using EvalsToInTime.trans (TM2.step M) 1 (m+n) _ _ _
        (one_step h₀) (EvalsToInTime.trans (TM2.step M) n m _ _ _ h₁ h₂)
  | @cond_true f a b s t n hf ha ih =>
      have h₀ : TM2.step M (configuration (some (embed (Program.cond f a b).start)) s) =
          some (configuration (some (embed (.inr (.inl a.start)))) s) := by
        simp only [configuration, TM2.step]; rw [hc]; simp [Program.start, Program.code, hf]
      have h₁ := ih M (fun x => embed (.inr (.inl x))) exit (fun l => hc (.inr (.inl l)))
      simpa only [Nat.add_comm] using EvalsToInTime.trans (TM2.step M) 1 n _ _ _ (one_step h₀) h₁
  | @cond_false f a b s t n hf hb ih =>
      have h₀ : TM2.step M (configuration (some (embed (Program.cond f a b).start)) s) =
          some (configuration (some (embed (.inr (.inr b.start)))) s) := by
        simp only [configuration, TM2.step]; rw [hc]; simp [Program.start, Program.code, hf]
      have h₁ := ih M (fun x => embed (.inr (.inr x))) exit (fun l => hc (.inr (.inr l)))
      simpa only [Nat.add_comm] using EvalsToInTime.trans (TM2.step M) 1 n _ _ _ (one_step h₀) h₁
  | @loop_false f body s hf =>
      apply one_step
      simp only [configuration, TM2.step]; rw [hc]; simp [Program.start, Program.code, hf]
  | @loop_true f body s t u n m hf ha hb iha ihb =>
      have h₀ : TM2.step M (configuration (some (embed (Program.loop f body).start)) s) =
          some (configuration (some (embed (.inr body.start))) s) := by
        simp only [configuration, TM2.step]; rw [hc]; simp [Program.start, Program.code, hf]
      have h₁ := iha M (fun x => embed (.inr x)) (some (embed (.inl ()))) (fun l => hc (.inr l))
      have h₂ := ihb M embed exit hc
      simpa only [Program.start, Nat.add_comm] using EvalsToInTime.trans (TM2.step M) 1 (m+n) _ _ _
        (one_step h₀) (EvalsToInTime.trans (TM2.step M) n m _ _ _ h₁ h₂)

namespace Program

variable [Fintype K] [Fintype σ] [∀ k, Fintype (Γ k)]

noncomputable def machine (p : Program Γ σ) (input output : K) (initial : σ) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := Γ
  Λ := p.Labels
  main := p.start
  σ := σ
  initialState := initial
  m := p.code id none

instance machine_alphabet_finite (p : Program Γ σ) (input output : K) (initial : σ)
    (k : K) : Fintype ((p.machine input output initial).Γ k) :=
  ‹∀ k, Fintype (Γ k)› k

noncomputable def compiles {p : Program Γ σ} {s t : Store Γ σ} {n : ℕ} (h : Exec p s n t)
    (input output : K) (initial : σ) :
    EvalsToInTime (p.machine input output initial).step
      (configuration (some p.start) s) (some (configuration none t)) n :=
  h.simulates (p.code id none) id none (fun _ => rfl)

end Program

end

variable {K α σ : Type} {Γ : K → Type} [decidableK : DecidableEq K]

abbrev SStore (K α σ : Type) := Store (fun _ : K => α) (Option α × σ)

abbrev SProgram (K α σ : Type) := Program (fun _ : K => α) (Option α × σ)

def Runs (p : Program Γ σ) (s t : Store Γ σ) (n : ℕ) : Prop :=
  ∃ m ≤ n, Nonempty (Exec p s m t)

namespace Runs

lemma atom (a : Action Γ σ) (s : Store Γ σ) : Runs (.atom a) s (a.run s) 1 :=
  ⟨1,le_rfl,⟨.atom a s⟩⟩

lemma atom_of (a : Action Γ σ) (s t : Store Γ σ) (h : a.run s = t) : Runs (.atom a) s t 1 :=
  h ▸ atom a s

lemma mono {p : Program Γ σ} {s t : Store Γ σ} {m n : ℕ}
    (h : Runs p s t m) (hn : m ≤ n) : Runs p s t n := by
  rcases h with ⟨a,ha,⟨h⟩⟩
  exact ⟨a,ha.trans hn,⟨h⟩⟩

lemma seq {a b : Program Γ σ} {s t u : Store Γ σ} {m n : ℕ}
    (ha : Runs a s t m) (hb : Runs b t u n) : Runs (.seq a b) s u (1+(m+n)) := by
  rcases ha with ⟨ma,hma,⟨ha⟩⟩
  rcases hb with ⟨nb,hnb,⟨hb⟩⟩
  exact ⟨1+(ma+nb),by omega,⟨.seq ha hb⟩⟩

lemma loop_false {f : σ → Bool} {b : Program Γ σ} {s : Store Γ σ}
    (h : f s.control = false) : Runs (.loop f b) s s 1 := ⟨1,le_rfl,⟨.loop_false h⟩⟩

lemma loop_true {f : σ → Bool} {b : Program Γ σ} {s t u : Store Γ σ} {m n : ℕ}
    (h : f s.control = true) (ha : Runs b s t m) (hb : Runs (.loop f b) t u n) :
    Runs (.loop f b) s u (1+(m+n)) := by
  rcases ha with ⟨ma,hma,⟨ha⟩⟩
  rcases hb with ⟨nb,hnb,⟨hb⟩⟩
  exact ⟨1+(ma+nb),by omega,⟨.loop_true h ha hb⟩⟩

lemma cond_true {f : σ → Bool} {a b : Program Γ σ} {s t : Store Γ σ} {n : ℕ}
    (hf : f s.control = true) (h : Runs a s t n) : Runs (.cond f a b) s t (1+n) := by
  rcases h with ⟨m,hm,⟨h⟩⟩
  exact ⟨1+m,by omega,⟨.cond_true hf h⟩⟩

lemma cond_false {f : σ → Bool} {a b : Program Γ σ} {s t : Store Γ σ} {n : ℕ}
    (hf : f s.control = false) (h : Runs b s t n) : Runs (.cond f a b) s t (1+n) := by
  rcases h with ⟨m,hm,⟨h⟩⟩
  exact ⟨1+m,by omega,⟨.cond_false hf h⟩⟩

lemma loop_steps {f : σ → Bool} {body : Program Γ σ} (states : ℕ → Store Γ σ) (n b : ℕ)
    (guard : ∀ i < n, f (states i).control = true)
    (stop : f (states n).control = false)
    (step : ∀ i < n, Runs body (states i) (states (i+1)) b) :
    Runs (.loop f body) (states 0) (states n) ((b+1)*n+1) := by
  induction n generalizing states with
  | zero => simpa using Runs.loop_false stop
  | succ n ih =>
      have h := Runs.loop_true (guard 0 (by omega)) (step 0 (by omega))
        (ih (fun i => states (i+1)) (fun i hi => guard (i+1) (by omega)) stop
          (fun i hi => step (i+1) (by omega)))
      convert h using 1 ; first | rfl | ring

end Runs

namespace Store

omit K σ Γ in
@[ext] lemma ext'
    {K : Type}
    {σ : Type}
    {Γ : K → Type}
    [DecidableEq K] {s t : Store Γ σ} (h : s.control = t.control) (g : s.stk = t.stk) : s = t := by
  cases s; cases t; simp_all

end Store

namespace Macros

variable [inhabitedα : Inhabited α]

def state (v : σ) (buf : Option α) (w : K → List α) : SStore K α σ := ⟨(buf,v),w⟩

def peek (i : K) : SProgram K α σ := .atom (.peek i (fun c a => (a,c.2)) .done)

def moveBody (i j : K) (f : σ → α → α) : SProgram K α σ :=
 .atom (.pop i (fun c _ => c) (.push j (fun c => f c.2 (c.1.getD default))
   (.peek i (fun c a => (a,c.2)) .done)))

def moveLoop (i j : K) (f : σ → α → α) : SProgram K α σ :=
 .loop (fun c => c.1.isSome) (moveBody i j f)

def moveRev (i j : K) (f : σ → α → α) : SProgram K α σ :=
 .seq (peek i) (moveLoop i j f)

omit K α in
lemma update_comm
    {K : Type}
    {α : Type}
    [DecidableEq K]
    [Inhabited α] (w : K → List α) (i j : K) (hi : i ≠ j) (a b : List α) :
  Function.update (Function.update w i a) j b = Function.update (Function.update w j b) i a := by
  exact Function.update_comm hi a b w

lemma moveLoop_runs (i j : K) (hij : i ≠ j) (f : σ → α → α) (v : σ)
    (w : K → List α) (xs ys : List α) :
    Runs (moveLoop i j f)
      (state v xs.head? (Function.update (Function.update w i xs) j ys))
      (state v none (Function.update (Function.update w i []) j ((xs.map (f v)).reverse ++ ys)))
      (2*xs.length+1) := by
  induction xs generalizing ys with
  | nil =>
      simpa only [moveLoop,List.head?_nil,List.map_nil,List.reverse_nil,List.nil_append,List.length_nil,
        Nat.mul_zero,Nat.zero_add] using
        Runs.loop_false (b := moveBody i j f) (f := fun c => c.1.isSome)
          (s := state v none (Function.update (Function.update w i []) j ys)) rfl
  | cons a xs ih =>
      have hbody : Runs (moveBody i j f)
          (state v (some a) (Function.update (Function.update w i (a::xs)) j ys))
          (state v xs.head? (Function.update (Function.update w i xs) j (f v a :: ys))) 1 := by
        unfold moveBody
        apply Runs.atom_of
        apply Store.ext'
        · simp [Action.run, state, Function.update, hij, Ne.symm hij]
        · simp only [Action.run, state, Option.getD_some]
          funext k
          by_cases hki : k = i
          · subst k; simp [Function.update, hij]
          · by_cases hkj : k = j
            · subst k; simp [Function.update, Ne.symm hij]
            · simp [Function.update, hki,hkj]
      have h := Runs.loop_true (f := fun c : Option α × σ => c.1.isSome) rfl
        hbody (ih (f v a :: ys))
      convert h using 1 <;> simp [moveLoop,List.map_cons,List.reverse_cons,List.append_assoc] ; omega

lemma moveRev_runs (i j : K) (hij : i ≠ j) (f : σ → α → α) (v : σ) (buf : Option α)
    (w : K → List α) (xs ys : List α) :
    Runs (moveRev i j f)
      (state v buf (Function.update (Function.update w i xs) j ys))
      (state v none (Function.update (Function.update w i []) j ((xs.map (f v)).reverse ++ ys)))
      (2*xs.length+3) := by
  have hp : Runs (peek i)
      (state v buf (Function.update (Function.update w i xs) j ys))
      (state v xs.head? (Function.update (Function.update w i xs) j ys)) 1 := by
    unfold peek
    apply Runs.atom_of
    simp [Action.run, state, Function.update, hij]
  convert hp.seq (moveLoop_runs i j hij f v w xs ys) using 1 <;> first | rfl | omega

def clearBody (i : K) : SProgram K α σ :=
  .atom (.pop i (fun c _ => c) (.peek i (fun c a => (a,c.2)) .done))

def clearLoop (i : K) : SProgram K α σ := .loop (fun c => c.1.isSome) (clearBody i)

def clear (i : K) : SProgram K α σ := .seq (peek i) (clearLoop i)

omit K α σ in
lemma clearLoop_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i : K) (v : σ) (w : K → List α) (xs : List α) :
    Runs (clearLoop i) (state v xs.head? (Function.update w i xs))
      (state v none (Function.update w i [])) (2*xs.length+1) := by
  induction xs with
  | nil => exact Runs.loop_false rfl
  | cons a xs ih =>
      have hb : Runs (clearBody i) (state v (some a) (Function.update w i (a::xs)))
          (state v xs.head? (Function.update w i xs)) 1 := by
        apply Runs.atom_of
        simp [Action.run,state]
      have h := Runs.loop_true (f := fun c : Option α × σ => c.1.isSome) rfl hb ih
      convert h using 1 <;> first | rfl | simp only [List.length_cons]; omega

omit K α σ in
lemma clear_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i : K) (v : σ) (buf : Option α) (w : K → List α) (xs : List α) :
    Runs (clear i) (state v buf (Function.update w i xs))
      (state v none (Function.update w i [])) (2*xs.length+3) := by
  have hb : Runs (peek i) (state v buf (Function.update w i xs))
      (state v xs.head? (Function.update w i xs)) 1 := by
    apply Runs.atom_of
    simp [Action.run,state]
  convert hb.seq (clearLoop_runs i v w xs) using 1 <;> first | rfl | omega

def dupeBody (i j k : K) : SProgram K α σ :=
 .atom (.pop i (fun c _ => c) (.push j (fun c => c.1.getD default)
   (.push k (fun c => c.1.getD default) (.peek i (fun c a => (a,c.2)) .done))))

def dupeLoop (i j k : K) : SProgram K α σ :=
 .loop (fun c => c.1.isSome) (dupeBody i j k)

def dupeRev (i j k : K) : SProgram K α σ := .seq (peek i) (dupeLoop i j k)

lemma dupeLoop_runs (i j k : K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : σ) (w : K → List α) (xs ys zs : List α) :
    Runs (dupeLoop i j k)
      (state v xs.head? (Function.update (Function.update (Function.update w i xs) j ys) k zs))
      (state v none (Function.update (Function.update (Function.update w i []) j (xs.reverse ++ ys))
        k (xs.reverse ++ zs))) (2*xs.length+1) := by
  induction xs generalizing ys zs with
  | nil => simpa only [dupeLoop,List.head?_nil,List.reverse_nil,List.nil_append,List.length_nil,
        Nat.mul_zero,Nat.zero_add] using
        (Runs.loop_false (f := fun c : Option α × σ => c.1.isSome) (b := dupeBody i j k)
          (s := state v none (Function.update (Function.update (Function.update w i []) j ys) k zs)) rfl)
  | cons a xs ih =>
      have hb : Runs (dupeBody i j k)
          (state v (some a) (Function.update (Function.update (Function.update w i (a::xs)) j ys) k zs))
          (state v xs.head? (Function.update (Function.update (Function.update w i xs) j (a::ys)) k (a::zs))) 1 := by
        apply Runs.atom_of
        apply Store.ext'
        · simp [Action.run,state,Function.update,hij,hik,Ne.symm hij,Ne.symm hik]
        · simp only [Action.run,state,Option.getD_some]
          funext l
          by_cases hi : l = i
          · subst l; simp [Function.update,hij,hik,]
          · by_cases hj : l = j
            · subst l; simp [Function.update,hjk,Ne.symm hij,]
            · by_cases hk : l = k
              · subst l; simp [Function.update,Ne.symm hik,Ne.symm hjk]
              · simp [Function.update,hi,hj,hk]
      have h := Runs.loop_true (f := fun c : Option α × σ => c.1.isSome) rfl hb
        (ih (a::ys) (a::zs))
      convert h using 1 <;> first | rfl | (simp [List.reverse_cons,List.append_assoc] <;> omega)

lemma dupeRev_runs (i j k : K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : σ) (buf : Option α) (w : K → List α) (xs ys zs : List α) :
    Runs (dupeRev i j k)
      (state v buf (Function.update (Function.update (Function.update w i xs) j ys) k zs))
      (state v none (Function.update (Function.update (Function.update w i []) j (xs.reverse ++ ys))
        k (xs.reverse ++ zs))) (2*xs.length+3) := by
  have hp : Runs (peek i)
      (state v buf (Function.update (Function.update (Function.update w i xs) j ys) k zs))
      (state v xs.head? (Function.update (Function.update (Function.update w i xs) j ys) k zs)) 1 := by
    apply Runs.atom_of
    simp [Action.run,state,Function.update,hij,hik]
  convert hp.seq (dupeLoop_runs i j k hij hik hjk v w xs ys zs) using 1 <;> first | rfl | omega

def copy (i j scratch : K) : SProgram K α σ :=
 .seq (moveRev i scratch (fun _ a => a)) (dupeRev scratch i j)

lemma copy_runs (i j k : K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : σ) (buf : Option α) (w : K → List α) (xs ys : List α) :
    Runs (copy i j k)
      (state v buf (Function.update (Function.update (Function.update w k []) i xs) j ys))
      (state v none (Function.update (Function.update (Function.update w k []) i xs) j (xs ++ ys)))
      (4*xs.length+7) := by
  have hm := moveRev_runs i k hik (fun (_ : σ) a => a) v buf (Function.update w j ys) xs []
  have hd := dupeRev_runs k i j (Ne.symm hik) (Ne.symm hjk) hij v none w xs.reverse [] ys
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at hm hd
  have hm' : Runs (moveRev i k (fun (_ : σ) a => a))
      (state v buf (Function.update (Function.update (Function.update w k []) i xs) j ys))
      (state v none (Function.update (Function.update (Function.update w k xs.reverse) i []) j ys))
      (2*xs.length+3) := by
    convert hm using 1 <;> congr 1 <;> funext l <;>
      by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;>
      simp_all [Function.update]
  convert hm'.seq hd using 1 <;> first | rfl | omega

end Macros

end CPTSeparation.StackLang

namespace CPTSeparation.StackLang.Macros

section

variable {K α σ : Type} [DecidableEq K] [inhabitedα : Inhabited α]

def rowLoop (i j : K) (f : σ → Option α → Option α) : SProgram K (Option α) σ :=
  .loop (fun c => (c.1.bind id).isSome) (moveBody i j f)

def moveRow (i j : K) (f : σ → Option α → Option α) : SProgram K (Option α) σ :=
 .seq (peek i) (.seq (rowLoop i j f) (.atom (.pop i (fun c _ => (none,c.2)) .done)))

omit K α σ in
lemma rowLoop_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i j : K) (hij : i ≠ j) (f : σ → Option α → Option α) (v : σ)
    (w : K → List (Option α)) (xs : List α) (suffix ys : List (Option α)) :
    Runs (rowLoop i j f)
      (state v (xs.map some ++ none::suffix).head?
        (Function.update (Function.update w i (xs.map some ++ none::suffix)) j ys))
      (state v (some none) (Function.update (Function.update w i (none::suffix))
        j ((xs.map (fun x => f v (some x))).reverse ++ ys))) (2*xs.length+1) := by
  induction xs generalizing ys with
  | nil =>
      simpa only [rowLoop,List.map_nil,List.nil_append,List.head?_cons,List.reverse_nil,
        List.length_nil,Nat.mul_zero,Nat.zero_add] using
        (Runs.loop_false (f := fun c : Option (Option α) × σ => (c.1.bind id).isSome)
          (b := moveBody i j f)
          (s := state v (some none) (Function.update (Function.update w i (none::suffix)) j ys)) rfl)
  | cons a xs ih =>
      have hb : Runs (moveBody i j f)
          (state v (some (some a)) (Function.update
            (Function.update w i (some a :: (xs.map some ++ none::suffix))) j ys))
          (state v (xs.map some ++ none::suffix).head? (Function.update
            (Function.update w i (xs.map some ++ none::suffix)) j (f v (some a)::ys))) 1 := by
        apply Runs.atom_of
        apply Store.ext'
        · simp [Action.run,state,Function.update,hij,Ne.symm hij]
        · simp only [Action.run,state,Option.getD_some]
          funext k
          by_cases hi : k = i
          · subst k; simp [Function.update,hij]
          · by_cases hj : k = j
            · subst k; simp [Function.update,Ne.symm hij]
            · simp [Function.update,hi,hj]
      have h := Runs.loop_true (f := fun c : Option (Option α) × σ => (c.1.bind id).isSome)
        rfl hb (ih (f v (some a)::ys))
      convert h using 1 <;> first | rfl | (simp [List.map_cons,List.reverse_cons,List.append_assoc] <;> omega)

omit K α σ in
lemma moveRow_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i j : K) (hij : i ≠ j) (f : σ → Option α → Option α) (v : σ)
    (buf : Option (Option α)) (w : K → List (Option α)) (xs : List α)
    (suffix ys : List (Option α)) :
    Runs (moveRow i j f)
      (state v buf (Function.update (Function.update w i (xs.map some ++ none::suffix)) j ys))
      (state v none (Function.update (Function.update w i suffix)
        j ((xs.map (fun x => f v (some x))).reverse ++ ys))) (2*xs.length+5) := by
  have hp : Runs (peek i)
      (state v buf (Function.update (Function.update w i (xs.map some ++ none::suffix)) j ys))
      (state v (xs.map some ++ none::suffix).head?
        (Function.update (Function.update w i (xs.map some ++ none::suffix)) j ys)) 1 := by
    apply Runs.atom_of
    simp [Action.run,state,Function.update,hij]
  have hf : Runs (.atom (.pop i (fun (c : Option (Option α) × σ) _ => (none,c.2)) .done))
      (state v (some none) (Function.update (Function.update w i (none::suffix))
        j ((xs.map (fun x => f v (some x))).reverse ++ ys)))
      (state v none (Function.update (Function.update w i suffix)
        j ((xs.map (fun x => f v (some x))).reverse ++ ys))) 1 := by
    apply Runs.atom_of
    apply Store.ext'
    · rfl
    · funext k
      by_cases hi : k = i
      · subst k; simp [Action.run,state,Function.update,hij]
      · simp [Action.run,state,Function.update,hi]
  convert hp.seq ((rowLoop_runs i j hij f v w xs suffix ys).seq hf) using 1 <;> first | rfl | omega

def skipRowLoop (i : K) : SProgram K (Option α) σ :=
  .loop (fun c => (c.1.bind id).isSome) (clearBody i)

def skipRow (i : K) : SProgram K (Option α) σ :=
  .seq (peek i) (.seq (skipRowLoop i) (.atom (.pop i (fun c _ => (none,c.2)) .done)))

omit K α σ in
lemma skipRowLoop_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i : K) (v : σ) (w : K → List (Option α)) (xs : List α)
    (suffix : List (Option α)) :
    Runs (skipRowLoop i)
      (state v (xs.map some ++ none::suffix).head?
        (Function.update w i (xs.map some ++ none::suffix)))
      (state v (some none) (Function.update w i (none::suffix))) (2*xs.length+1) := by
  induction xs with
  | nil => exact Runs.loop_false rfl
  | cons a xs ih =>
      have hb : Runs (clearBody i)
          (state v (some (some a)) (Function.update w i (some a :: (xs.map some ++ none::suffix))))
          (state v (xs.map some ++ none::suffix).head?
            (Function.update w i (xs.map some ++ none::suffix))) 1 := by
        apply Runs.atom_of
        simp [Action.run,state]
      have h := Runs.loop_true (f := fun c : Option (Option α) × σ => (c.1.bind id).isSome) rfl hb ih
      convert h using 1 <;> first | rfl | (simp only [List.length_cons]; omega)

omit K α σ in
lemma skipRow_runs
    {K : Type}
    {α : Type}
    {σ : Type}
    [DecidableEq K]
    [Inhabited α] (i : K) (v : σ) (buf : Option (Option α))
    (w : K → List (Option α)) (xs : List α) (suffix : List (Option α)) :
    Runs (skipRow i) (state v buf (Function.update w i (xs.map some ++ none::suffix)))
      (state v none (Function.update w i suffix)) (2*xs.length+5) := by
  have hp : Runs (peek i) (state v buf (Function.update w i (xs.map some ++ none::suffix)))
      (state v (xs.map some ++ none::suffix).head? (Function.update w i (xs.map some ++ none::suffix))) 1 := by
    apply Runs.atom_of
    simp [Action.run,state]
  have hf : Runs (.atom (.pop i (fun (c : Option (Option α) × σ) _ => (none,c.2)) .done))
      (state v (some none) (Function.update w i (none::suffix)))
      (state v none (Function.update w i suffix)) 1 := by
    apply Runs.atom_of
    simp [Action.run,state]
  convert hp.seq ((skipRowLoop_runs i v w xs suffix).seq hf) using 1 <;> first | rfl | omega

end

variable {K α τ : Type} [DecidableEq K] [Inhabited α]

def zipRowBody (i o p b : K) (f : τ → α → α → α) :
    SProgram K (Option α) (Option α × τ) :=
 .atom (.pop i (fun c a => (a,c.2))
  (.pop p (fun c a => (c.1,(a.getD none,c.2.2)))
   (.push b (fun c => c.2.1)
    (.push o (fun c => some (f c.2.2 ((c.1.bind id).getD default) (c.2.1.getD default)))
     (.peek i (fun c a => (a,(none,c.2.2))) .done)))))

def zipRowLoop (i o p b : K) (f : τ → α → α → α) :
    SProgram K (Option α) (Option α × τ) :=
 .loop (fun c => (c.1.bind id).isSome) (zipRowBody i o p b f)

def zipRow (i o p b : K) (f : τ → α → α → α) :
    SProgram K (Option α) (Option α × τ) :=
 .seq (peek i) (.seq (zipRowLoop i o p b f)
   (.atom (.pop i (fun c _ => (none,c.2)) .done)))

lemma zipRowLoop_runs (i o p b : K) (hio : i ≠ o) (hip : i ≠ p) (hib : i ≠ b)
    (hop : o ≠ p) (hob : o ≠ b) (hpb : p ≠ b)
    (f : τ → α → α → α) (v : τ) (w : K → List (Option α))
    (xs ys : List α) (hlen : xs.length = ys.length)
    (suffix os bs : List (Option α)) :
    Runs (zipRowLoop i o p b f)
      (state ((none : Option α),v) (xs.map some ++ none::suffix).head?
        (Function.update (Function.update (Function.update (Function.update w i
          (xs.map some ++ none::suffix)) o os) p (ys.map some)) b bs))
      (state ((none : Option α),v) (some none)
        (Function.update (Function.update (Function.update (Function.update w i (none::suffix))
          o (((List.zipWith (f v) xs ys).map some).reverse ++ os)) p [])
          b ((ys.map some).reverse ++ bs))) (2*xs.length+1) := by
  induction xs generalizing ys os bs with
  | nil =>
      have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst ys
      simpa only [zipRowLoop,List.map_nil,List.nil_append,List.head?_cons,List.zipWith_nil_left,List.reverse_nil,
        List.length_nil,Nat.mul_zero,Nat.zero_add] using
        (Runs.loop_false (f := fun c : Option (Option α) × (Option α × τ) => (c.1.bind id).isSome)
          (b := zipRowBody i o p b f)
          (s := state ((none : Option α),v) (some none) (Function.update (Function.update
            (Function.update (Function.update w i (none::suffix)) o os) p []) b bs)) rfl)
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := by simpa using hlen
          have hb : Runs (zipRowBody i o p b f)
              (state ((none : Option α),v) (some (some a)) (Function.update (Function.update (Function.update
                (Function.update w i (some a :: (xs.map some ++ none::suffix))) o os)
                  p (some y :: ys.map some)) b bs))
              (state ((none : Option α),v) (xs.map some ++ none::suffix).head?
                (Function.update (Function.update (Function.update (Function.update w i
                  (xs.map some ++ none::suffix)) o (some (f v a y)::os)) p (ys.map some)) b (some y::bs))) 1 := by
            apply Runs.atom_of
            apply Store.ext'
            · simp [Action.run,state,Function.update,hio,hip,hib,hop,hob,hpb,
                Ne.symm hio,Ne.symm hip,Ne.symm hib,Ne.symm hpb]
            · simp only [Action.run,state]
              funext k
              by_cases hi : k = i <;> by_cases ho : k = o <;>
                by_cases hp : k = p <;> by_cases hb : k = b <;>
                simp_all [Function.update,Ne.symm hio,Ne.symm hip,Ne.symm hib,Ne.symm hop,Ne.symm hob,Ne.symm hpb]
          have h := Runs.loop_true (f := fun c : Option (Option α) × (Option α × τ) => (c.1.bind id).isSome)
            rfl hb (ih ys hlen' (some (f v a y)::os) (some y::bs))
          convert h using 1 <;> first | rfl |
            (simp [List.map_cons,List.reverse_cons,List.append_assoc] <;> omega)

lemma zipRow_runs (i o p b : K) (hio : i ≠ o) (hip : i ≠ p) (hib : i ≠ b)
    (hop : o ≠ p) (hob : o ≠ b) (hpb : p ≠ b)
    (f : τ → α → α → α) (v : τ) (buf : Option (Option α)) (w : K → List (Option α))
    (xs ys : List α) (hlen : xs.length = ys.length)
    (suffix os bs : List (Option α)) :
    Runs (zipRow i o p b f)
      (state ((none : Option α),v) buf
        (Function.update (Function.update (Function.update (Function.update w i
          (xs.map some ++ none::suffix)) o os) p (ys.map some)) b bs))
      (state ((none : Option α),v) none
        (Function.update (Function.update (Function.update (Function.update w i suffix)
          o (((List.zipWith (f v) xs ys).map some).reverse ++ os)) p [])
          b ((ys.map some).reverse ++ bs))) (2*xs.length+5) := by
  have hp : Runs (peek i)
      (state ((none : Option α),v) buf (Function.update (Function.update (Function.update (Function.update w i
          (xs.map some ++ none::suffix)) o os) p (ys.map some)) b bs))
      (state ((none : Option α),v) (xs.map some ++ none::suffix).head?
        (Function.update (Function.update (Function.update (Function.update w i
          (xs.map some ++ none::suffix)) o os) p (ys.map some)) b bs)) 1 := by
    apply Runs.atom_of
    simp [Action.run,state,Function.update,hio,hip,hib]
  have hf : Runs (.atom (.pop i (fun (c : Option (Option α) × (Option α × τ)) _ => (none,c.2)) .done))
      (state ((none : Option α),v) (some none)
        (Function.update (Function.update (Function.update (Function.update w i (none::suffix))
          o (((List.zipWith (f v) xs ys).map some).reverse ++ os)) p [])
          b ((ys.map some).reverse ++ bs)))
      (state ((none : Option α),v) none
        (Function.update (Function.update (Function.update (Function.update w i suffix)
          o (((List.zipWith (f v) xs ys).map some).reverse ++ os)) p [])
          b ((ys.map some).reverse ++ bs))) 1 := by
    apply Runs.atom_of
    apply Store.ext'
    · rfl
    · simp only [Action.run,state]
      funext k
      by_cases hi : k = i <;> by_cases ho : k = o <;>
        by_cases hp : k = p <;> by_cases hb : k = b <;>
        simp_all [Function.update,Ne.symm hio,Ne.symm hip,Ne.symm hib,Ne.symm hop,Ne.symm hob,Ne.symm hpb]
  convert hp.seq ((zipRowLoop_runs i o p b hio hip hib hop hob hpb f v w xs ys hlen suffix os bs).seq hf)
    using 1 <;> first | rfl | omega

end CPTSeparation.StackLang.Macros

end OAI
