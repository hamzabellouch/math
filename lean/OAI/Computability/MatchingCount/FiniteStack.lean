import OAI.Combinatorics.PerfectMatching.Model

namespace OAI

section

namespace BinaryMatching.StackCode

abbrev Store (r : ℕ) := Fin r → List Bool

inductive Instr (r : ℕ) (L : Type)
  | go : L → Instr r L
  | push : Fin r → Bool → L → Instr r L
  | pop : Fin r → L → Instr r L
  | branch : Fin r → L → L → L → Instr r L

namespace Instr
variable {r : ℕ} {L L' : Type}

def map (f : L → L') : Instr r L → Instr r L'
  | .go q => .go (f q)
  | .push k b q => .push k b (f q)
  | .pop k q => .pop k (f q)
  | .branch k e z o => .branch k (f e) (f z) (f o)

def eval : Instr r L → Store r → L × Store r
  | .go q,s => (q,s)
  | .push k b q,s => (q,Function.update s k (b::s k))
  | .pop k q,s => (q,Function.update s k (s k).tail)
  | .branch k e z o,s => ((s k).head?.elim e (fun b => if b then o else z),s)

@[simp] theorem eval_map (f : L → L') (i : Instr r L) (s : Store r) :
    (i.map f).eval s = (f (i.eval s).1,(i.eval s).2) := by
  cases i <;> simp only [map,eval]
  rename_i k e z o
  cases h : (s k).head? with
  | none => rfl
  | some b => cases b <;> rfl

abbrev Stmt (r : ℕ) (L : Type) := Turing.TM2.Stmt (fun _ : Fin r => Bool) L (Option Bool)

def target (q : Option L) : Stmt r L :=
  .load (fun _ => none) (q.elim .halt (fun l => .goto (fun _ => l)))

def translate : Instr r (Option L) → Stmt r L
  | .go q => target q
  | .push k b q => .push k (fun _ => b) (target q)
  | .pop k q => .pop k (fun _ _ => none) (target q)
  | .branch k e z o => .peek k (fun _ h => h)
      (.branch Option.isNone (target e) (.branch (fun h => h.getD false) (target o) (target z)))

@[simp] theorem target_step (q : Option L) (v : Option Bool) (s : Store r) :
    Turing.TM2.stepAux (target q) v s = ⟨q,none,s⟩ := by cases q <;> rfl

@[simp] theorem translate_step (i : Instr r (Option L)) (v : Option Bool) (s : Store r) :
    Turing.TM2.stepAux i.translate v s = ⟨(i.eval s).1,none,(i.eval s).2⟩ := by
  cases i with
  | go q => exact target_step q v s
  | push k b q => simp only [translate,Turing.TM2.stepAux,target_step,eval]
  | pop k q => simp only [translate,Turing.TM2.stepAux,target_step,eval]
  | branch k e z o =>
    simp only [translate,Turing.TM2.stepAux,target_step,eval]
    cases h : (s k).head? with
    | none => rfl
    | some b => cases b <;> rfl
end Instr

structure Block (r : ℕ) where
  Label : Type
  finite : Fintype Label
  entry : Label
  code : Label → Instr r (Option Label)

attribute [instance] Block.finite

inductive Steps {r : ℕ} {L : Type} (code : L → Instr r (Option L)) :
    Option L → Store r → Option L → Store r → ℕ → Prop
  | refl (q s) : Steps code q s q s 0
  | next (q s q' s' t)
      (rest : Steps code ((code q).eval s).1 ((code q).eval s).2 q' s' t) :
      Steps code (some q) s q' s' (t+1)

namespace Steps
variable {r : ℕ} {L L' : Type} {code : L → Instr r (Option L)}

theorem trans {q s q' s' q'' s'' t u}
    (h : Steps code q s q' s' t) (h' : Steps code q' s' q'' s'' u) :
    Steps code q s q'' s'' (t+u) := by
  induction h with
  | refl => simpa using h'
  | next q s q' s' t h ih => simpa [Nat.add_right_comm] using Steps.next q s _ _ _ (ih h')

theorem map (code' : L' → Instr r (Option L')) (f : L → L') (last : Option L')
    (hcode : ∀ l, code' (f l)=(code l).map (fun q => q.elim last (some ∘ f)))
    {q s q' s' t} (h : Steps code q s q' s' t) :
    Steps code' (q.elim last (some ∘ f)) s (q'.elim last (some ∘ f)) s' t := by
  induction h with
  | refl => exact .refl _ _
  | next q s q' s' t h ih =>
    apply Steps.next
    simpa only [hcode,Instr.eval_map] using ih

abbrev cfg (q : Option L) (s : Store r) :
    Turing.TM2.Cfg (fun _ : Fin r => Bool) L (Option Bool) := ⟨q,none,s⟩

theorem simulation {q s q' s' t} (h : Steps code q s q' s' t) :
    (fun o => o.bind (Turing.TM2.step (fun l => (code l).translate)))^[t]
      (some (cfg q s)) = some (cfg q' s') := by
  induction h with
  | refl => rfl
  | next q s q' s' t h ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,Turing.TM2.step,Instr.translate_step] using ih
end Steps

namespace Block
variable {r : ℕ}

def primitive (i : Instr r Unit) : Block r where
  Label := Unit
  finite := inferInstance
  entry := ()
  code _ := i.map (fun _ => none)

def seq (a b : Block r) : Block r where
  Label := a.Label ⊕ b.Label
  finite := inferInstance
  entry := .inl a.entry
  code := fun l => match l with
    | .inl q => (a.code q).map (fun t => t.elim (some (.inr b.entry)) (fun u => some (.inl u)))
    | .inr q => (b.code q).map (Option.map Sum.inr)

def cases (k : Fin r) (e z o : Block r) : Block r where
  Label := Unit ⊕ (e.Label ⊕ (z.Label ⊕ o.Label))
  finite := inferInstance
  entry := .inl ()
  code := fun l => match l with
    | .inl _ => .branch k (some (.inr (.inl e.entry)))
        (some (.inr (.inr (.inl z.entry)))) (some (.inr (.inr (.inr o.entry))))
    | .inr (.inl q) => (e.code q).map (Option.map (Sum.inr ∘ Sum.inl))
    | .inr (.inr (.inl q)) => (z.code q).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inl))
    | .inr (.inr (.inr q)) => (o.code q).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inr))

def loop (k : Fin r) (b : Block r) : Block r where
  Label := Unit ⊕ b.Label
  finite := inferInstance
  entry := .inl ()
  code := fun l => match l with
    | .inl _ => .branch k none (some (.inr b.entry)) (some (.inr b.entry))
    | .inr q => (b.code q).map (fun t => t.elim (some (.inl ())) (fun u => some (.inr u)))

abbrev Runs (b : Block r) (s s' : Store r) (t : ℕ) : Prop :=
  Steps b.code (some b.entry) s none s' t

theorem primitive_runs (i : Instr r Unit) (s : Store r) :
    (primitive i).Runs s (i.eval s).2 1 := by
  apply Steps.next
  simp only [primitive,Instr.eval_map]
  exact .refl _ _

theorem seq_runs (a b : Block r) {s s' s'' : Store r} {t u : ℕ}
    (ha : a.Runs s s' t) (hb : b.Runs s' s'' u) : (a.seq b).Runs s s'' (t+u) := by
  have h₁ := ha.map (a.seq b).code Sum.inl (some (Sum.inr b.entry)) (fun _ => rfl)
  have h₂ := hb.map (a.seq b).code Sum.inr none (by
    intro l
    change (b.code l).map _ = (b.code l).map _
    congr 1
    funext t
    cases t <;> rfl)
  exact h₁.trans h₂

def machine (b : Block r) (input output : Fin r) : Turing.FinTM2 where
  K := Fin r
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := b.Label
  main := b.entry
  σ := Option Bool
  initialState := none
  m l := (b.code l).translate

theorem machine_finite (b : Block r) (input output : Fin r) (k : (b.machine input output).K) :
    Finite ((b.machine input output).Γ k) := by
  change Finite Bool
  infer_instance

def machine_runs (b : Block r) (input output : Fin r) (s s' : List Bool) {t : ℕ}
    (h : b.Runs (Function.update (fun _ => []) input s)
      (Function.update (fun _ => []) output s') t) :
    Turing.TM2OutputsInTime (b.machine input output) s (some s') t := by
  refine ⟨⟨t,?_⟩,le_rfl⟩
  have hini : Turing.initList (b.machine input output) s =
      Steps.cfg (some b.entry) (Function.update (fun _ => []) input s) := by
    simp only [Turing.initList,machine,Steps.cfg]
    congr 1
    funext k
    by_cases hk : k=input
    · subst k; rfl
    · simp [Function.update,hk]
  have hout : Turing.haltList (b.machine input output) s' =
      Steps.cfg none (Function.update (fun _ => []) output s') := by
    simp only [Turing.haltList,machine,Steps.cfg]
    congr 1
    funext k
    by_cases hk : k=output
    · subst k; rfl
    · simp [Function.update,hk]
  change (fun o => o.bind (Turing.TM2.step (fun l => (b.code l).translate)))^[t]
    (some (Turing.initList (b.machine input output) s)) =
    some (Turing.haltList (b.machine input output) s')
  rw [hini,hout]
  exact h.simulation
end Block
end BinaryMatching.StackCode
end

end OAI
