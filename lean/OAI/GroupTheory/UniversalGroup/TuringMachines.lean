import OAI.GroupTheory.UniversalGroup.StackPrograms

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman.MicroTM2
open Turing Function Relation
variable {K Γ Λ σ : Type} [DecidableEq K]
abbrev Stmt (K Γ Λ σ : Type) := TM2.Stmt (fun _ : K ↦ Γ) Λ σ
abbrev Cfg (K Γ Λ σ : Type) := (K → List Γ) × (Option (Stmt K Γ Λ σ) × σ)

variable (M : Λ → Stmt K Γ Λ σ)

def step : Cfg K Γ Λ σ → Option (Cfg K Γ Λ σ)
  | (_,none,_) => none
  | (S,some q,v) => some <| match q with
    | .push k f r => (update S k (f v :: S k),some r,v)
    | .peek k f r => (S,some r,f v (S k).head?)
    | .pop k f r => (update S k (S k).tail,some r,f v (S k).head?)
    | .load f r => (S,some r,f v)
    | .branch f r t => (S,some (if f v then r else t),v)
    | .goto f => (S,some (M (f v)),v)
    | .halt => (S,none,v)

def translate (c : TM2.Cfg (fun _ : K ↦ Γ) Λ σ) : Cfg K Γ Λ σ :=
  (c.stk,Option.map M c.l,c.var)

def project : Cfg K Γ Λ σ → TM2.Cfg (fun _ : K ↦ Γ) Λ σ
  | (S,none,v) => ⟨none,v,S⟩
  | (S,some q,v) => TM2.stepAux q v S

theorem reaches_stepAux (q : Stmt K Γ Λ σ) (v : σ) (S : K → List Γ) :
    StateTransition.Reaches (step M) (S,some q,v) (translate M (TM2.stepAux q v S)) := by
  induction q generalizing v S with
  | push k f r ih =>
    exact ReflTransGen.head rfl (ih v (update S k (f v :: S k)))
  | peek k f r ih => exact ReflTransGen.head rfl (ih (f v (S k).head?) S)
  | pop k f r ih =>
    exact ReflTransGen.head rfl (ih (f v (S k).head?) (update S k (S k).tail))
  | load f r ih => exact ReflTransGen.head rfl (ih (f v) S)
  | branch f r t ihr iht =>
    cases h : f v
    · simp only [TM2.stepAux,h,Bool.cond_false]
      exact ReflTransGen.head
        (show (S,some t,v) ∈ step M (S,some (.branch f r t),v) by simp [step,h]) (iht v S)
    · simp only [TM2.stepAux,h,Bool.cond_true]
      exact ReflTransGen.head
        (show (S,some r,v) ∈ step M (S,some (.branch f r t),v) by simp [step,h]) (ihr v S)
  | goto f => exact ReflTransGen.single rfl
  | halt => exact ReflTransGen.single rfl

theorem translate_step {c d : TM2.Cfg (fun _ : K ↦ Γ) Λ σ} (h : d ∈ TM2.step M c) :
    StateTransition.Reaches (step M) (translate M c) (translate M d) := by
  rcases c with ⟨_ | l,v,S⟩
  · simp [TM2.step] at h
  · have hh : d = TM2.stepAux (M l) v S := by simpa [TM2.step] using h.symm
    subst d
    exact reaches_stepAux M (M l) v S

theorem translate_reaches {c d : TM2.Cfg (fun _ : K ↦ Γ) Λ σ}
    (h : TM2.Reaches M c d) : StateTransition.Reaches (step M) (translate M c) (translate M d) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail h hd ih => exact ih.trans (translate_step M hd)

theorem project_step {c d : Cfg K Γ Λ σ} (h : d ∈ step M c) :
    TM2.Reaches M (project c) (project d) := by
  rcases c with ⟨S,_ | q,v⟩
  · simp [step] at h
  · cases q with
    | push k f r =>
      have hd : d = (update S k (f v :: S k),some r,v) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.refl
    | peek k f r =>
      have hd : d = (S,some r,f v (S k).head?) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.refl
    | pop k f r =>
      have hd : d = (update S k (S k).tail,some r,f v (S k).head?) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.refl
    | load f r =>
      have hd : d = (S,some r,f v) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.refl
    | branch f r t =>
      have hd : d = (S,some (if f v then r else t),v) := by simpa [step] using h.symm
      subst d
      cases h : f v <;> simp [project,TM2.stepAux,h,TM2.Reaches] <;> exact ReflTransGen.refl
    | goto f =>
      have hd : d = (S,some (M (f v)),v) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.single rfl
    | halt =>
      have hd : d = (S,none,v) := by simpa [step] using h.symm
      subst d
      exact ReflTransGen.refl

theorem project_reaches {c d : Cfg K Γ Λ σ} (h : StateTransition.Reaches (step M) c d) :
    TM2.Reaches M (project c) (project d) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail h hd ih => exact ih.trans (project_step M hd)

theorem reaches_project_translate (c : TM2.Cfg (fun _ : K ↦ Γ) Λ σ) :
    TM2.Reaches M c (project (translate M c)) := by
  rcases c with ⟨_ | l,v,S⟩
  · exact ReflTransGen.refl
  · exact ReflTransGen.single rfl

theorem reaches_halt_iff (c : TM2.Cfg (fun _ : K ↦ Γ) Λ σ) (S : K → List Γ) (v : σ) :
    TM2.Reaches M c ⟨none,v,S⟩ ↔
      StateTransition.Reaches (step M) (translate M c) (S,none,v) := by
  constructor
  · exact translate_reaches M
  · intro h
    exact (reaches_project_translate M c).trans (project_reaches M h)

end Higman.MicroTM2

namespace Higman.TM2StackCompiler
open Turing Function AffineStack StackProgram MicroTM2 Relation
variable {K Γ Λ σ G : Type} [DecidableEq K] [Group G]

def readOp (pop : Bool) : Option Γ → Op Γ
  | none => .empty
  | some a => if pop then .pop a else .peek a

lemma readOp_rel (pop : Bool) (a : Option Γ) (s t : List Γ) :
    (readOp pop a).Rel s t ↔ a = s.head? ∧ t = (if pop then s.tail else s) := by
  cases pop <;> cases a <;> cases s <;> simp [readOp,Op.Rel] <;> aesop

lemma readAction_rel (pop : Bool) (a : Option Γ) (k : K) (S T : K → List Γ) :
    (Action.onStack k (readOp pop a)).Rel S T ↔
      a = (S k).head? ∧ T = (if pop then update S k (S k).tail else S) := by
  simp only [Action.Rel,readOp_rel]
  constructor
  · rintro ⟨t,⟨h,rfl⟩,rfl⟩
    refine ⟨h,?_⟩
    cases pop <;> simp
  · rintro ⟨h,rfl⟩
    refine ⟨if pop then (S k).tail else S k,⟨h,rfl⟩,?_⟩
    cases pop <;> simp

def rawAction (q : Stmt K Γ Λ σ) (v : σ) (a : Option Γ) : Action K Γ :=
  match q with
  | .push k f _ => .onStack k (.push (f v))
  | .peek k _ _ => .onStack k (readOp false a)
  | .pop k _ _ => .onStack k (readOp true a)
  | _ => .idle

def rawTarget (M : Λ → Stmt K Γ Λ σ) (q : Stmt K Γ Λ σ) (v : σ) (a : Option Γ) :
    Option (Stmt K Γ Λ σ) × σ :=
  match q with
  | .push _ _ r => (some r,v)
  | .peek _ f r => (some r,f v a)
  | .pop _ f r => (some r,f v a)
  | .load f r => (some r,f v)
  | .branch f r t => (some (if f v then r else t),v)
  | .goto f => (some (M (f v)),v)
  | .halt => (none,v)

variable (M : Λ → Stmt K Γ Λ σ)

lemma raw_sound (q : Stmt K Γ Λ σ) (v : σ) (a : Option Γ) (S T : K → List Γ)
    (h : (rawAction q v a).Rel S T) :
    (T,rawTarget M q v a) ∈ MicroTM2.step M (S,some q,v) := by
  cases q with
  | push k f r =>
    obtain ⟨t,ht,rfl⟩ := h
    cases ht
    rfl
  | peek k f r =>
    obtain ⟨ha,rfl⟩ := (readAction_rel false a k S T).mp h
    simp [rawTarget,MicroTM2.step,ha]
  | pop k f r =>
    obtain ⟨ha,rfl⟩ := (readAction_rel true a k S T).mp h
    simp [rawTarget,MicroTM2.step,ha]
  | load f r | branch f r t | goto f | halt =>
    cases h
    rfl

lemma raw_complete (q : Stmt K Γ Λ σ) (v : σ) (S : K → List Γ) (d : Cfg K Γ Λ σ)
    (h : d ∈ MicroTM2.step M (S,some q,v)) :
    ∃ a, (rawAction q v a).Rel S d.1 ∧ d.2 = rawTarget M q v a := by
  cases q with
  | push k f r =>
    have hd : d = (update S k (f v :: S k),some r,v) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨none,⟨f v :: S k,rfl,rfl⟩,rfl⟩
  | peek k f r =>
    have hd : d = (S,some r,f v (S k).head?) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨(S k).head?,(readAction_rel false _ k S S).mpr ⟨rfl,rfl⟩,rfl⟩
  | pop k f r =>
    have hd : d = (update S k (S k).tail,some r,f v (S k).head?) := by
      simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨(S k).head?,(readAction_rel true _ k S _).mpr ⟨rfl,rfl⟩,rfl⟩
  | load f r =>
    have hd : d = (S,some r,f v) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨none,rfl,rfl⟩
  | branch f r t =>
    have hd : d = (S,some (if f v then r else t),v) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨none,rfl,rfl⟩
  | goto f =>
    have hd : d = (S,some (M (f v)),v) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨none,rfl,rfl⟩
  | halt =>
    have hd : d = (S,none,v) := by simpa [MicroTM2.step] using h.symm
    subst d
    exact ⟨none,rfl,rfl⟩

variable (L : Finset Λ) (hL : ∀ l ∈ L, TM2.SupportsStmt L (M l))

include hL in
omit [DecidableEq K] in
lemma target_mem (q : Stmt K Γ Λ σ) (hq : some q ∈ TM2.stmts M L) (v : σ) (a : Option Γ) :
    (rawTarget M q v a).1 ∈ TM2.stmts M L := by
  classical
  have hs : TM2.SupportsStmt L q := by
    obtain ⟨l,hl,hh⟩ := Finset.mem_biUnion.mp (Finset.some_mem_insertNone.mp hq)
    exact TM2.stmts₁_supportsStmt_mono hh (hL l hl)
  cases q with
  | push k f r | peek k f r | pop k f r | load f r =>
    exact TM2.stmts_trans (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
  | branch f r t =>
    dsimp [rawTarget]
    split_ifs
    · exact TM2.stmts_trans (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
    · exact TM2.stmts_trans (by simp [TM2.stmts₁,TM2.stmts₁_self]) hq
  | goto f =>
    apply Finset.some_mem_insertNone.mpr
    apply Finset.mem_biUnion.mpr
    exact ⟨f v,hs v,TM2.stmts₁_self⟩
  | halt => exact Finset.none_mem_insertNone

abbrev State := {q : Option (Stmt K Γ Λ σ) // q ∈ TM2.stmts M L} × σ
abbrev Edge := {q : Stmt K Γ Λ σ // some q ∈ TM2.stmts M L} × σ × Option Γ

noncomputable instance [Fintype σ] : Fintype (State M L) := inferInstance
noncomputable instance [Fintype σ] [Fintype Γ] : Fintype (Edge M L) := by
  classical
  have : Fintype {q : Stmt K Γ Λ σ // some q ∈ TM2.stmts M L} :=
    Fintype.ofInjective (fun q ↦ (⟨some q.val,q.property⟩ :
      {q : Option (Stmt K Γ Λ σ) // q ∈ TM2.stmts M L})) (by
        intro q r h; exact Subtype.ext (Option.some.inj (congrArg Subtype.val h)))
  exact inferInstance

noncomputable def compile (e : Edge M L) : Instruction K Γ G (State M L) where
  source := (⟨some e.1.val,e.1.property⟩,e.2.1)
  target := (⟨(rawTarget M e.1.val e.2.1 e.2.2).1,target_mem M L hL _ e.1.property _ _⟩,
    (rawTarget M e.1.val e.2.1 e.2.2).2)
  action := rawAction e.1.val e.2.1 e.2.2
  weight := 1

def forget (c : (K → List Γ) × State M L) : Cfg K Γ Λ σ :=
  (c.1,c.2.1.val,c.2.2)

lemma compile_sound (e : Edge M L) (S T : K → List Γ)
    (h : (compile (G := G) M L hL e).action.Rel S T) :
    forget M L (T,(compile (G := G) M L hL e).target) ∈
      MicroTM2.step M (forget M L (S,(compile (G := G) M L hL e).source)) :=
  raw_sound M e.1.val e.2.1 e.2.2 S T h

lemma compile_complete (c : (K → List Γ) × State M L) (d : Cfg K Γ Λ σ)
    (h : d ∈ MicroTM2.step M (forget M L c)) :
    ∃ e : Edge M L, c.2 = (compile (G := G) M L hL e).source ∧
      (compile (G := G) M L hL e).action.Rel c.1 d.1 ∧
      forget M L (d.1,(compile (G := G) M L hL e).target) = d := by
  rcases c with ⟨S,⟨_ | q,hq⟩,v⟩
  · simp [forget,MicroTM2.step] at h
  · obtain ⟨a,ha,hd⟩ := raw_complete M q v S d h
    refine ⟨(⟨q,hq⟩,v,a),rfl,ha,?_⟩
    change (d.1,rawTarget M q v a) = d
    rw [← hd]

lemma run_sound {seed : (K → List Γ) × State M L} {s : List (Edge M L)}
    {c : (K → List Γ) × State M L}
    (h : Run (compile (G := G) M L hL) seed s c) :
    StateTransition.Reaches (MicroTM2.step M) (forget M L seed) (forget M L c) := by
  induction h with
  | start => exact ReflTransGen.refl
  | step e S T hr h ih => exact ih.tail (compile_sound M L hL e S T hr)

lemma reaches_complete {seed : (K → List Γ) × State M L} {d : Cfg K Γ Λ σ}
    (h : StateTransition.Reaches (MicroTM2.step M) (forget M L seed) d) :
    ∃ s c, Run (compile (G := G) M L hL) seed s c ∧ forget M L c = d := by
  induction h with
  | refl => exact ⟨[],seed,Run.start,rfl⟩
  | @tail d f hr hd ih =>
    obtain ⟨s,c,hc,rfl⟩ := ih
    obtain ⟨e,he,ha,hf⟩ := compile_complete (G := G) M L hL c f hd
    refine ⟨e::s,(f.1,(compile (G := G) M L hL e).target),?_,hf⟩
    apply Run.step e c.1 f.1 ha
    simpa only [← he] using hc

omit [DecidableEq K] in
@[simp] lemma weights_one (s : List (Edge M L)) :
    HistoryMachine.value (fun e ↦ (compile (G := G) M L hL e).weight) s = 1 := by
  induction s with
  | nil => rfl
  | cons e s ih => simpa only [HistoryMachine.value,compile,mul_one] using ih

end Higman.TM2StackCompiler

end UniversalFinitelyPresentedProof

end OAI
