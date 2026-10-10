import OAI.Computability.Scheduling.RegisterMachine

namespace OAI

section

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def Code.rename (f : V → W) : Code V → Code W
  | .skip => .skip
  | .nil dst => .nil (f dst)
  | .pair dst a b => .pair (f dst) (f a) (f b)
  | .select head dst src => .select head (f dst) (f src)
  | .copy dst src => .copy (f dst) (f src)
  | .seq p q => .seq (p.rename f) (q.rename f)
  | .branch src p q => .branch (f src) (p.rename f) (q.rename f)
  | .loop src p => .loop (f src) (p.rename f)

noncomputable def overlay (f : V → W) (s : V → Data) (base : W → Data) : W → Data :=
  Function.extend f s base

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_apply {f : V → W} (hf : Function.Injective f) (s : V → Data) (base : W → Data) (i : V) :
    overlay f s base (f i) = s i := hf.extend_apply s base i

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_out {f : V → W} (s : V → Data) (base : W → Data) {j : W} (hj : ¬∃ i, f i = j) :
    overlay f s base j = base j := Function.extend_apply' s base j hj

theorem overlay_update {f : V → W} (hf : Function.Injective f) (s : V → Data) (base : W → Data)
    (i : V) (d : Data) :
    overlay f (Function.update s i d) base = Function.update (overlay f s base) (f i) d := by
  funext j
  by_cases hj : ∃ a, f a = j
  · obtain ⟨a,rfl⟩ := hj
    by_cases ha : a = i <;> simp [overlay_apply hf,ha,hf.eq_iff]
  · have hn : j ≠ f i := fun h => hj ⟨i,h.symm⟩
    rw [overlay_out _ _ hj,Function.update_of_ne hn,overlay_out _ _ hj]

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_of_agree (f : V → W) (s : V → Data) (base : W → Data)
    (h : ∀ i, base (f i) = s i) : overlay f s base = base := by
  funext j
  by_cases hj : ∃ a, f a = j
  · unfold overlay Function.extend
    simp only [dite_eq_left hj]
    rw [← h]
    congr 1
    exact Classical.choose_spec hj
  · exact overlay_out s base hj

theorem Eval.rename {p : Code V} {s t : V → Data} {n : ℕ} (h : Eval p s t n)
    {f : V → W} (hf : Function.Injective f) (base : W → Data) :
    Eval (p.rename f) (overlay f s base) (overlay f t base) n := by
  induction h with
  | skip s => exact Eval.skip _
  | nil dst s => simpa only [Code.rename,overlay_update hf,overlay_apply hf] using Eval.nil (f dst) (overlay f s base)
  | pair dst a b s => simpa only [Code.rename,overlay_update hf,overlay_apply hf] using Eval.pair (f dst) (f a) (f b) (overlay f s base)
  | select head dst src s => simpa only [Code.rename,overlay_update hf,overlay_apply hf] using Eval.select head (f dst) (f src) (overlay f s base)
  | copy dst src s => simpa only [Code.rename,overlay_update hf,overlay_apply hf] using Eval.copy (f dst) (f src) (overlay f s base)
  | seq _ _ ih ih' => exact Eval.seq ih ih'
  | branch_true hs _ ih => exact Eval.branch_true (by simpa only [overlay_apply hf] using hs) ih
  | branch_false hs _ ih => exact Eval.branch_false (by simpa only [overlay_apply hf] using hs) ih
  | loop_stop hs => exact Eval.loop_stop (by simpa only [overlay_apply hf] using hs)
  | loop_step hs _ _ ih ih' => exact Eval.loop_step (by simpa only [overlay_apply hf] using hs) ih ih'

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def Bounded (p : Code V) (s t : V → Data) (bound : ℕ) : Prop :=
  ∃ n ≤ bound, Eval p s t n

theorem Eval.bounded {p : Code V} {s t : V → Data} {n : ℕ} (h : Eval p s t n) : Bounded p s t n :=
  ⟨n,le_rfl,h⟩

theorem Bounded.mono {p : Code V} {s t : V → Data} {n m : ℕ} (h : Bounded p s t n) (h' : n ≤ m) :
    Bounded p s t m := by
  obtain ⟨a,ha,he⟩ := h
  exact ⟨a,ha.trans h',he⟩

theorem Bounded.seq {p q : Code V} {s t u : V → Data} {n m : ℕ}
    (h : Bounded p s t n) (h' : Bounded q t u m) : Bounded (.seq p q) s u (n+m+1) := by
  obtain ⟨a,ha,he⟩ := h
  obtain ⟨b,hb,he'⟩ := h'
  exact ⟨a+b+1,by omega,Eval.seq he he'⟩

def join (s : V → Data) (t : W → Data) : V ⊕ W → Data := Sum.elim s t

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem join_inl (s : V → Data) (t : W → Data) (i : V) : join s t (.inl i) = s i := rfl
omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem join_inr (s : V → Data) (t : W → Data) (i : W) : join s t (.inr i) = t i := rfl

theorem join_update_left (s : V → Data) (t : W → Data) (i : V) (d : Data) :
    Function.update (join s t) (.inl i) d = join (Function.update s i d) t := by
  funext j
  cases j with
  | inl j => by_cases hj : j = i <;> simp [hj]
  | inr j => simp

theorem join_update_right (s : V → Data) (t : W → Data) (i : W) (d : Data) :
    Function.update (join s t) (.inr i) d = join s (Function.update t i d) := by
  funext j
  cases j with
  | inl j => simp
  | inr j => by_cases hj : j = i <;> simp [hj]

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_left (s s' : V → Data) (t : W → Data) : overlay Sum.inl s (join s' t) = join s t := by
  funext j
  cases j with
  | inl j => exact overlay_apply Sum.inl_injective _ _ _
  | inr j => exact overlay_out _ _ (by simp)

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_right (s : V → Data) (t t' : W → Data) : overlay Sum.inr t (join s t') = join s t := by
  funext j
  cases j with
  | inl j => exact overlay_out _ _ (by simp)
  | inr j => exact overlay_apply Sum.inr_injective _ _ _

theorem Bounded.left {p : Code V} {s t : V → Data} {n : ℕ}
    (h : Bounded p s t n) (u : W → Data) : Bounded (p.rename Sum.inl) (join s u) (join t u) n := by
  obtain ⟨m,hm,he⟩ := h
  refine ⟨m,hm,?_⟩
  simpa only [overlay_left] using he.rename Sum.inl_injective (join s u)

theorem Bounded.right {p : Code W} {s t : W → Data} {n : ℕ}
    (h : Bounded p s t n) (u : V → Data) : Bounded (p.rename Sum.inr) (join u s) (join u t) n := by
  obtain ⟨m,hm,he⟩ := h
  refine ⟨m,hm,?_⟩
  simpa only [overlay_right] using he.rename Sum.inr_injective (join u s)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree

def zeroStore (V : Type) : V → Data := fun _ => .nil

def start {V : Type} [DecidableEq V] (input : V) (x : Data) : V → Data :=
  Function.update (zeroStore V) input x

def finish {V : Type} [DecidableEq V] (input output : V) (x y : Data) : V → Data :=
  Function.update (start input x) output y

structure Routine (f : Data → Data) (charge : Data → ℕ) where
  Vars : Type
  finiteVars : Fintype Vars
  decVars : DecidableEq Vars
  input : Vars
  output : Vars
  distinct : input ≠ output
  code : Code Vars
  correct : ∀ x, Bounded code (start input x) (finish input output x (f x)) (charge x)

attribute [instance] Routine.finiteVars Routine.decVars

namespace Routine
variable {f g : Data → Data} {charge charge' : Data → ℕ}

def mono (R : Routine f charge) (h : ∀ x, charge x ≤ charge' x) : Routine f charge' :=
  { R with correct := fun x => (R.correct x).mono (h x) }

def identity : Routine id (fun x => x.size+2) where
  Vars := Bool
  finiteVars := inferInstance
  decVars := inferInstance
  input := false
  output := true
  distinct := by decide
  code := .copy true false
  correct x := by
    simpa [finish,start,zeroStore,Nat.add_comm] using (Eval.copy true false (start false x)).bounded

def nil : Routine (fun _ => Data.nil) (fun _ => 2) where
  Vars := Bool
  finiteVars := inferInstance
  decVars := inferInstance
  input := false
  output := true
  distinct := by decide
  code := .nil true
  correct x := by
    simpa [finish,start,zeroStore] using (Eval.nil true (start false x)).bounded

def select (head : Bool) : Routine (fun x => if head then x.head else x.tail) (fun x => x.size+2) where
  Vars := Bool
  finiteVars := inferInstance
  decVars := inferInstance
  input := false
  output := true
  distinct := by decide
  code := .select head true false
  correct x := by
    simpa [finish,start,zeroStore,Nat.add_comm] using (Eval.select head true false (start false x)).bounded

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

@[simp] theorem start_input (input : V) (x : Data) : start input x input = x := by simp [start]
@[simp] theorem start_other {input i : V} (x : Data) (hi : i ≠ input) : start input x i = .nil := by simp [start,hi,zeroStore]
@[simp] theorem finish_output (input output : V) (x y : Data) : finish input output x y output = y := by simp [finish]
@[simp] theorem finish_input {input output : V} (h : input ≠ output) (x y : Data) : finish input output x y input = x := by simp [finish,start,h]

theorem start_left (input : V) (x : Data) :
    start (Sum.inl input : V ⊕ W) x = join (start input x) (zeroStore W) := by
  funext j
  cases j with
  | inl j => by_cases hj : j = input <;> simp [hj,start,zeroStore]
  | inr j => simp [start,zeroStore]

theorem start_right (input : W) (x : Data) :
    start (Sum.inr input : V ⊕ W) x = join (zeroStore V) (start input x) := by
  funext j
  cases j with
  | inl j => simp [start,zeroStore]
  | inr j => by_cases hj : j = input <;> simp [hj,start,zeroStore]

theorem finish_lr (input : V) (output : W) (x y : Data) :
    finish (Sum.inl input) (Sum.inr output) x y = join (start input x) (start output y) := by
  rw [finish,start_left,join_update_right]
  rfl

theorem reset_output {input output : V} (h : input ≠ output) (x y : Data) :
    Function.update (finish input output x y) output .nil = start input x := by
  have he : start input x output = .nil := start_other x h.symm
  rw [finish,Function.update_idem,← he,Function.update_eq_self]

theorem reset_input {input output : V} (h : input ≠ output) (x y : Data) :
    Function.update (finish input output x y) input .nil = start output y := by
  funext i
  by_cases hi : i = input
  · subst i; simp [start,h,zeroStore]
  · by_cases ho : i = output
    · subst i; simp [hi,start]
    · simp [finish,start,hi,ho,zeroStore]

namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}

def compCode (R : Routine f c) (S : Routine g d) : Code (R.Vars ⊕ S.Vars) :=
  .seq (R.code.rename Sum.inl)
    (.seq (.copy (.inr S.input) (.inl R.output))
    (.seq (S.code.rename Sum.inr)
    (.seq (.nil (.inl R.output)) (.nil (.inr S.input)))))

def comp (R : Routine f c) (S : Routine g d) :
    Routine (g ∘ f) (fun x => c x+d (f x)+10*((f x).size+1)) where
  Vars := R.Vars ⊕ S.Vars
  finiteVars := inferInstance
  decVars := inferInstance
  input := .inl R.input
  output := .inr S.output
  distinct := by simp
  code := compCode R S
  correct x := by
    let a := start R.input x
    let a' := finish R.input R.output x (f x)
    let b := start S.input (f x)
    let b' := finish S.input S.output (f x) (g (f x))
    have h₁ : Bounded (R.code.rename Sum.inl) (join a (zeroStore S.Vars)) (join a' (zeroStore S.Vars)) (c x) :=
      (R.correct x).left _
    have h₂ : Bounded (.copy (.inr S.input) (.inl R.output))
        (join a' (zeroStore S.Vars)) (join a' b) ((f x).size+2) := by
      simpa [join_update_right,a',b,zeroStore,start,Nat.add_comm] using
        (Eval.copy (.inr S.input) (.inl R.output) (join a' (zeroStore S.Vars))).bounded
    have h₃ : Bounded (S.code.rename Sum.inr) (join a' b) (join a' b') (d (f x)) :=
      (S.correct (f x)).right _
    have h₄ : Bounded (.nil (.inl R.output)) (join a' b') (join a b') (1+(f x).size) := by
      simpa only [join_update_left,a',a,reset_output R.distinct,join_inl,finish_output] using
        (Eval.nil (.inl R.output) (join a' b')).bounded
    have h₅ : Bounded (.nil (.inr S.input)) (join a b') (join a (start S.output (g (f x)))) (1+(f x).size) := by
      simpa only [join_update_right,b',reset_input S.distinct,join_inr,finish_input S.distinct] using
        (Eval.nil (.inr S.input) (join a b')).bounded
    have hh := h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))
    simpa only [start_left,finish_lr,Function.comp_apply] using
      (show Bounded (compCode R S) (join a (zeroStore S.Vars)) (join a (start S.output (g (f x))))
        (c x+d (f x)+10*((f x).size+1)) from hh.mono (by omega))

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree

variable {V : Type} [DecidableEq V]
theorem reset_start (input : V) (x : Data) :
    Function.update (start input x) input .nil = zeroStore V := by
  funext i
  by_cases h : i = input <;> simp [start,zeroStore,h]

namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}

def pairCode (R : Routine f c) (S : Routine g d) : Code ((R.Vars ⊕ S.Vars) ⊕ Unit) :=
  .seq ((R.code.rename Sum.inl).rename Sum.inl)
    (.seq (.copy (.inl (.inr S.input)) (.inl (.inl R.input)))
    (.seq ((S.code.rename Sum.inr).rename Sum.inl)
    (.seq (.pair (.inr ()) (.inl (.inl R.output)) (.inl (.inr S.output)))
    (.seq (.nil (.inl (.inl R.output)))
    (.seq (.nil (.inl (.inr S.output))) (.nil (.inl (.inr S.input))))))))

def pair (R : Routine f c) (S : Routine g d) :
    Routine (fun x => Data.pair (f x) (g x))
      (fun x => c x+d x+20*(x.size+(f x).size+(g x).size+1)) where
  Vars := (R.Vars ⊕ S.Vars) ⊕ Unit
  finiteVars := inferInstance
  decVars := inferInstance
  input := .inl (.inl R.input)
  output := .inr ()
  distinct := by simp
  code := pairCode R S
  correct x := by
    let a := start R.input x
    let a' := finish R.input R.output x (f x)
    let b := start S.input x
    let b' := finish S.input S.output x (g x)
    let z := zeroStore Unit
    let o := start () (Data.pair (f x) (g x))
    have h₁ := ((R.correct x).left (zeroStore S.Vars)).left z
    have h₂ : Bounded (.copy (.inl (.inr S.input)) (.inl (.inl R.input)))
        (join (join a' (zeroStore S.Vars)) z) (join (join a' b) z) (x.size+2) := by
      simpa [join_update_left,join_update_right,a',b,zeroStore,start,R.distinct,Nat.add_comm] using
        (Eval.copy (.inl (.inr S.input)) (.inl (.inl R.input))
          (join (join a' (zeroStore S.Vars)) z)).bounded
    have h₃ := ((S.correct x).right a').left z
    have h₄ : Bounded (.pair (.inr ()) (.inl (.inl R.output)) (.inl (.inr S.output)))
        (join (join a' b') z) (join (join a' b') o) (2+(f x).size+(g x).size) := by
      simpa [join_update_right,o,z,zeroStore,start,a',b'] using
        (Eval.pair (.inr ()) (.inl (.inl R.output)) (.inl (.inr S.output))
          (join (join a' b') z)).bounded
    have h₅ : Bounded (.nil (.inl (.inl R.output)))
        (join (join a' b') o) (join (join a b') o) (1+(f x).size) := by
      simpa only [join_update_left,a',a,reset_output R.distinct,join_inl,finish_output] using
        (Eval.nil (.inl (.inl R.output)) (join (join a' b') o)).bounded
    have h₆ : Bounded (.nil (.inl (.inr S.output)))
        (join (join a b') o) (join (join a b) o) (1+(g x).size) := by
      simpa only [join_update_left,join_update_right,b',b,reset_output S.distinct,join_inr,join_inl,finish_output] using
        (Eval.nil (.inl (.inr S.output)) (join (join a b') o)).bounded
    have h₇ : Bounded (.nil (.inl (.inr S.input)))
        (join (join a b) o) (join (join a (zeroStore S.Vars)) o) (1+x.size) := by
      simpa only [join_update_left,join_update_right,b,reset_start,join_inr,join_inl,start_input] using
        (Eval.nil (.inl (.inr S.input)) (join (join a b) o)).bounded
    have hh := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq (h₆.seq h₇)))))
    simpa only [start_left,finish_lr] using
      (show Bounded (pairCode R S) (join (join a (zeroStore S.Vars)) z)
        (join (join a (zeroStore S.Vars)) o)
        (c x+d x+20*(x.size+(f x).size+(g x).size+1)) from hh.mono (by omega))

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {V : Type} [DecidableEq V]
theorem Bounded.loop_stop (src : V) (p : Code V) (s : V → Data)
    (h : (s src).nonempty = false) : Bounded (.loop src p) s s 1 :=
  (Eval.loop_stop h).bounded

theorem Bounded.loop_step {src : V} {p : Code V} {s t u : V → Data} {n m : ℕ}
    (h : (s src).nonempty = true) (hp : Bounded p s t n)
    (hq : Bounded (.loop src p) t u m) : Bounded (.loop src p) s u (n+m+1) := by
  obtain ⟨n',hn,he⟩ := hp
  obtain ⟨m',hm,he'⟩ := hq
  exact ⟨n'+m'+1,by omega,Eval.loop_step h he he'⟩
end ThreeMachine.StackCompiler.Tree

end

end OAI
