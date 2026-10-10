import OAI.Computability.Superstring.Schedule

namespace OAI

namespace Superstring.BitCode

abbrev Store (K : Type) := K → List Bool

/-- A finite-control bit-stack instruction. There is no unbounded internal
state and no operation on an entire stack other than one push/pop/peek. -/
inductive Instr (K L : Type)
  | push (k : K) (b : Bool) (next : L)
  | pop (k : K) (next : L)
  | branch (k : K) (empty low high : L)
  | jump (next : L)

namespace Instr

def map {K L M : Type} (f : L → M) : Instr K L → Instr K M
  | .push k b l => .push k b (f l)
  | .pop k l => .pop k (f l)
  | .branch k e l h => .branch k (f e) (f l) (f h)
  | .jump l => .jump (f l)

def run {K L : Type} [DecidableEq K] : Instr K L → Store K → L × Store K
  | .push k b l, s => (l, Function.update s k (b :: s k))
  | .pop k l, s => (l, Function.update s k (s k).tail)
  | .branch k e l h, s => (match (s k).head? with
      | none => e
      | some false => l
      | some true => h, s)
  | .jump l, s => (l, s)

@[simp] theorem run_map {K L M : Type} [DecidableEq K] (f : L → M)
    (i : Instr K L) (s : Store K) : (i.map f).run s = Prod.map f id (i.run s) := by
  cases i with
  | branch k e l h => cases hs : (s k).head? with
    | none => simp [map, run, hs]
    | some b => cases b <;> simp [map, run, hs]
  | _ => rfl


def emit {K L : Type} : Instr K (Option L) →
    Turing.TM2.Stmt (fun _ : K => Bool) L (Option Bool)
  | .push k b l => .push k (fun _ => b) (finish l)
  | .pop k l => .pop k (fun _ _ => none) (finish l)
  | .branch k e l h => .peek k (fun _ b => b)
      (.branch Option.isNone (finish e)
        (.branch (fun b => b.getD false) (finish h) (finish l)))
  | .jump l => finish l
where
  finish {K L : Type} (l : Option L) :
      Turing.TM2.Stmt (fun _ : K => Bool) L (Option Bool) :=
    .load (fun _ => none) (match l with | none => .halt | some x => .goto (fun _ => x))

theorem finish_step {K L : Type} [DecidableEq K] (l : Option L)
    (v : Option Bool) (s : Store K) :
    Turing.TM2.stepAux (emit.finish l) v s = ⟨l, none, s⟩ := by
  cases l <;> rfl

theorem emit_step {K L : Type} [DecidableEq K] (i : Instr K (Option L))
    (v : Option Bool) (s : Store K) :
    Turing.TM2.stepAux i.emit v s = ⟨(i.run s).1, none, (i.run s).2⟩ := by
  cases i with
  | push k b l => exact finish_step l v _
  | pop k l => exact finish_step l none _
  | branch k e l h =>
    cases hs : (s k).head? with
    | none => simp [emit, Turing.TM2.stepAux, hs, finish_step, run]
    | some b => cases b <;> simp [emit, Turing.TM2.stepAux, hs, finish_step, run]
  | jump l => exact finish_step l v s

end Instr

/-- Structured bit-stack code. Loops are ordinary operational loops, not
unbounded-cost primitives. Their iteration count is charged in `Exec`. -/
inductive Block (K : Type)
  | push (k : K) (b : Bool)
  | pop (k : K)
  | skip
  | branch (k : K) (empty low high : Block K)
  | seq (first second : Block K)
  | loop (k : K) (body : Block K)

namespace Block

def Label {K : Type} : Block K → Type
  | .push _ _ | .pop _ | .skip => Unit
  | .branch _ a b c => Unit ⊕ (Label a ⊕ Label b ⊕ Label c)
  | .seq a b => Label a ⊕ Label b
  | .loop _ a => Option (Label a)

instance labelFintype {K : Type} : (b : Block K) → Fintype b.Label
  | .push _ _ | .pop _ | .skip => inferInstanceAs (Fintype Unit)
  | .branch _ a b c => by
    letI := labelFintype a
    letI := labelFintype b
    letI := labelFintype c
    exact inferInstanceAs (Fintype (Unit ⊕ (Label a ⊕ Label b ⊕ Label c)))
  | .seq a b => by
    letI := labelFintype a
    letI := labelFintype b
    exact inferInstanceAs (Fintype (Label a ⊕ Label b))
  | .loop _ a => by
    letI := labelFintype a
    exact inferInstanceAs (Fintype (Option (Label a)))

instance labelDecidableEq {K : Type} : (b : Block K) → DecidableEq b.Label
  | .push _ _ | .pop _ | .skip => inferInstanceAs (DecidableEq Unit)
  | .branch _ a b c => by
    letI := labelDecidableEq a
    letI := labelDecidableEq b
    letI := labelDecidableEq c
    exact inferInstanceAs (DecidableEq (Unit ⊕ (Label a ⊕ Label b ⊕ Label c)))
  | .seq a b => by
    letI := labelDecidableEq a
    letI := labelDecidableEq b
    exact inferInstanceAs (DecidableEq (Label a ⊕ Label b))
  | .loop _ a => by
    letI := labelDecidableEq a
    exact inferInstanceAs (DecidableEq (Option (Label a)))

def start {K : Type} : (b : Block K) → b.Label
  | .push _ _ | .pop _ | .skip => ()
  | .branch _ _ _ _ => .inl ()
  | .seq a _ => .inl a.start
  | .loop _ _ => none

def code {K : Type} : (b : Block K) → b.Label → Instr K (Option b.Label)
  | .push k b, _ => .push k b none
  | .pop k, _ => .pop k none
  | .skip, _ => .jump none
  | .branch k a b c, .inl _ => .branch k
      (some (.inr (.inl a.start))) (some (.inr (.inr (.inl b.start))))
      (some (.inr (.inr (.inr c.start))))
  | .branch _ a _ _, .inr (.inl l) => (a.code l).map (Option.map (Sum.inr ∘ Sum.inl))
  | .branch _ _ b _, .inr (.inr (.inl l)) =>
      (b.code l).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inl))
  | .branch _ _ _ c, .inr (.inr (.inr l)) =>
      (c.code l).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inr))
  | .seq a b, .inl l => (a.code l).map (fun q =>
      match q with | none => some (.inr b.start) | some x => some (.inl x))
  | .seq _ b, .inr l => (b.code l).map (Option.map Sum.inr)
  | .loop k a, none => .branch k none (some (some a.start)) (some (some a.start))
  | .loop _ a, some l => (a.code l).map (fun q => some q)

end Block

end Superstring.BitCode

namespace Superstring.BitCode

variable {K : Type} [DecidableEq K]

/-- Exact execution in the finite-control graph, stopping before a halt label
is stepped. This is a finite trace, not an oracle for a computation. -/
inductive Steps {L : Type} (code : L → Instr K (Option L)) :
    (Option L × Store K) → ℕ → (Option L × Store K) → Prop
  | refl (c) : Steps code c 0 c
  | step (l : L) (s : Store K) {n d} (h : Steps code ((code l).run s) n d) :
      Steps code (some l, s) (n + 1) d

namespace Steps

variable {L M : Type} {code : L → Instr K (Option L)}

theorem trans {a b c} {m n : ℕ} (h : Steps code a m b) (h' : Steps code b n c) :
    Steps code a (m + n) c := by
  induction h with
  | refl => simpa using h'
  | step l s h ih => simpa only [Nat.add_assoc, Nat.add_comm 1] using step l s (ih h')

theorem map (f : Option L → Option M) (j : L → M)
    {big : M → Instr K (Option M)}
    (hl : ∀ l, f (some l) = some (j l))
    (hc : ∀ l, big (j l) = (code l).map f)
    {a b} {n} (h : Steps code a n b) :
    Steps big (Prod.map f id a) n (Prod.map f id b) := by
  induction h with
  | refl => exact .refl _
  | step l s h ih =>
    simp only [Prod.map, id_eq, hl] at *
    apply Steps.step
    simpa only [hc, Instr.run_map, Prod.map, id_eq] using ih

end Steps

namespace Block

/-- Big-step semantics with the exact number of primitive bit instructions. -/
inductive Exec : Block K → Store K → Store K → ℕ → Prop
  | push (k b s) : Exec (.push k b) s (Function.update s k (b :: s k)) 1
  | pop (k s) : Exec (.pop k) s (Function.update s k (s k).tail) 1
  | skip (s) : Exec .skip s s 1
  | branch_none {k a b c s t n} (h : (s k).head? = none) (run : Exec a s t n) :
      Exec (.branch k a b c) s t (n + 1)
  | branch_false {k a b c s t n} (h : (s k).head? = some false) (run : Exec b s t n) :
      Exec (.branch k a b c) s t (n + 1)
  | branch_true {k a b c s t n} (h : (s k).head? = some true) (run : Exec c s t n) :
      Exec (.branch k a b c) s t (n + 1)
  | seq {a b s t u m n} (first : Exec a s t m) (second : Exec b t u n) :
      Exec (.seq a b) s u (m + n)
  | loop_nil {k a s} (h : s k = []) : Exec (.loop k a) s s 1
  | loop_cons {k a s t u m n} (h : s k ≠ []) (body : Exec a s t m)
      (rest : Exec (.loop k a) t u n) : Exec (.loop k a) s u (m + n + 1)

theorem exec_steps {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n) :
    Steps b.code (some b.start, s) n (none, t) := by
  induction h with
  | push k b s => exact .step () s (.refl _)
  | pop k s => exact .step () s (.refl _)
  | skip s => exact .step () s (.refl _)
  | @branch_none k a b c s t n hh run ih =>
    apply Steps.step
    simp only [code, start, Instr.run, hh]
    exact ih.map (Option.map (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inl)
      (fun _ => rfl) (fun _ => rfl)
  | @branch_false k a b c s t n hh run ih =>
    apply Steps.step
    simp only [code, start, Instr.run, hh]
    exact ih.map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inl))
      (Sum.inr ∘ Sum.inr ∘ Sum.inl) (fun _ => rfl) (fun _ => rfl)
  | @branch_true k a b c s t n hh run ih =>
    apply Steps.step
    simp only [code, start, Instr.run, hh]
    exact ih.map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inr))
      (Sum.inr ∘ Sum.inr ∘ Sum.inr) (fun _ => rfl) (fun _ => rfl)
  | @seq a b s t u m n first second ih₁ ih₂ =>
    let f : Option a.Label → Option ((seq a b).Label) := fun q =>
      match q with | none => some (.inr b.start) | some x => some (.inl x)
    have h₁ : Steps (seq a b).code (some (.inl a.start), s) m (some (.inr b.start), t) :=
      ih₁.map f Sum.inl (fun _ => rfl) (fun _ => rfl)
    have h₂ : Steps (seq a b).code (some (.inr b.start), t) n (none, u) :=
      ih₂.map (Option.map Sum.inr) Sum.inr (fun _ => rfl) (fun _ => rfl)
    exact h₁.trans h₂
  | @loop_nil k a s hh =>
    apply Steps.step
    simpa only [code, start, Instr.run, hh, List.head?_nil] using
      (Steps.refl (code := code (.loop k a)) (none, s))
  | @loop_cons k a s t u m n hh body rest ih₁ ih₂ =>
    apply Steps.step
    have hstart : ((code (.loop k a)) none).run s = (some (some a.start), s) := by
      cases he : s k with
      | nil => exact False.elim (hh he)
      | cons x xs => cases x <;> simp only [code, Instr.run, he, List.head?_cons] <;> rfl
    dsimp only [start]
    rw [hstart]
    exact (ih₁.map some some (fun _ => rfl) (fun _ => rfl)).trans ih₂


def machine [Fintype K] (b : Block K) (input output : K) : Turing.FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := b.Label
  main := b.start
  σ := Option Bool
  initialState := none
  m l := (b.code l).emit

def pack {L : Type} (c : Option L × Store K) :
    Turing.TM2.Cfg (fun _ : K => Bool) L (Option Bool) := ⟨c.1, none, c.2⟩

theorem steps_iterate {L : Type} {code : L → Instr K (Option L)}
    {s t : Option L × Store K} {n : ℕ} (h : Steps code s n t) :
    (fun c => c.bind (Turing.TM2.step (fun l => (code l).emit)))^[n]
      (some (pack s)) = some (pack t) := by
  induction h with
  | refl => rfl
  | step l S h ih =>
    rw [Function.iterate_succ_apply]
    simpa only [pack, Option.bind_some, Turing.TM2.step, Instr.emit_step] using ih

def exec_machine [Fintype K] (b : Block K) (input output : K)
    {s t : Store K} {n : ℕ} (h : b.Exec s t n) :
    StateTransition.EvalsToInTime (b.machine input output).step
      (pack (some b.start, s)) (some (pack (none, t))) n :=
  ⟨⟨n, steps_iterate (exec_steps h)⟩, le_rfl⟩

end Block

end Superstring.BitCode

namespace Superstring.BitCode

variable {K : Type} [DecidableEq K]

/-- A single populated stack: the exact Mathlib initial/final convention. -/
def single (k : K) (w : List Bool) : Store K := fun j => if j = k then w else []

namespace Block

theorem init_eq [Fintype K] (b : Block K) (i o : K) (w : List Bool) :
    Turing.initList (b.machine i o) w = pack (some b.start, single i w) := by
  dsimp only [Turing.initList, machine, pack]
  apply congrArg (fun S : Store K => Turing.TM2.Cfg.mk (some b.start) none S)
  funext k
  by_cases h : k = i
  · subst k
    rfl
  · simp only [dite_eq_right h, single, ite_eq_right h]

theorem halt_eq [Fintype K] (b : Block K) (i o : K) (w : List Bool) :
    Turing.haltList (b.machine i o) w = pack (none, single o w) := by
  dsimp only [Turing.haltList, machine, pack]
  apply congrArg (fun S : Store K => Turing.TM2.Cfg.mk none none S)
  funext k
  by_cases h : k = o
  · subst k
    rfl
  · simp only [dite_eq_right h, single, ite_eq_right h]

/-- Execution with a polynomial clock gives a polynomial-time TM2 certificate. -/
noncomputable def certificate [Fintype K] {α β : Type}
    (ea : α → List Bool) (eb : β → List Bool) (f : α → β)
    (b : Block K) (i o : K) (P : Polynomial ℕ)
    (correct : ∀ a, ∃ n, n ≤ P.eval (ea a).length ∧
      b.Exec (single i (ea a)) (single o (eb (f a))) n) :
    Turing.TM2ComputableInPolyTime ea eb f where
  tm := b.machine i o
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := P
  outputsFun a := by
    let n := (correct a).choose
    have hn := (correct a).choose_spec
    refine ⟨⟨n, ?_⟩, hn.1⟩
    change (flip bind (b.machine i o).step)^[n]
      (some (Turing.initList (b.machine i o) ((ea a).map id))) =
        some (Turing.haltList (b.machine i o) ((eb (f a)).map id))
    have hi := init_eq b i o (ea a)
    have ho := halt_eq b i o (eb (f a))
    dsimp only [machine] at *
    simp only [List.map_id]
    rw [hi, ho]
    exact steps_iterate (exec_steps hn.2)

theorem certificate_finite [Fintype K] {α β : Type}
    (ea : α → List Bool) (eb : β → List Bool) (f : α → β)
    (b : Block K) (i o : K) (P : Polynomial ℕ)
    (correct : ∀ a, ∃ n, n ≤ P.eval (ea a).length ∧
      b.Exec (single i (ea a)) (single o (eb (f a))) n)
    (k : (b.certificate ea eb f i o P correct).tm.K) :
    Finite ((b.certificate ea eb f i o P correct).tm.Γ k) := inferInstanceAs (Finite Bool)

end Block

section Size
variable [Fintype K]

def size (s : Store K) : ℕ := ∑ k, (s k).length

theorem size_update (s : Store K) (k : K) (w : List Bool) :
    size (Function.update s k w) + (s k).length = size s + w.length := by
  classical
  have h₁ := Finset.sum_erase_add Finset.univ (fun j => (Function.update s k w j).length)
    (Finset.mem_univ k)
  have h₂ := Finset.sum_erase_add Finset.univ (fun j => (s j).length) (Finset.mem_univ k)
  have he : (∑ j ∈ Finset.univ.erase k, (Function.update s k w j).length) =
      ∑ j ∈ Finset.univ.erase k, (s j).length := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  simp only [he, Function.update_self] at h₁
  dsimp only [size]
  omega

theorem size_push (s : Store K) (k : K) (b : Bool) :
    size (Function.update s k (b :: s k)) = size s + 1 := by
  have hh := size_update s k (b :: s k)
  simp only [List.length_cons] at hh
  omega

theorem size_pop (s : Store K) (k : K) :
    size (Function.update s k (s k).tail) ≤ size s := by
  have hh := size_update s k (s k).tail
  simp only [List.length_tail] at hh
  omega

/-- Every actually executed primitive bit instruction increases total stored
length by at most one; branch tests and iterations do not hide bulk operations. -/
theorem Block.Exec.size_le {b : Block K} {s t : Store K} {n : ℕ}
    (h : b.Exec s t n) : size t ≤ size s + n := by
  induction h with
  | push k b s => exact le_of_eq (size_push s k b)
  | pop k s => exact (size_pop s k).trans (Nat.le_add_right _ _)
  | skip => omega
  | branch_none _ _ ih => omega
  | branch_false _ _ ih => omega
  | branch_true _ _ ih => omega
  | seq _ _ ih₁ ih₂ => omega
  | loop_nil => omega
  | loop_cons _ _ _ ih₁ ih₂ => omega

end Size

end Superstring.BitCode

end OAI
