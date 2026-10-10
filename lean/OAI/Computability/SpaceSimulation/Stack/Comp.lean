import OAI.Computability.SpaceSimulation.StackMachine

namespace OAI

/-! Sequencing elementary stack computations. -/
namespace Fifths.SM
variable {X J K Y Z : Type}

def peek (f : Reads X J → (K → Option Bool) → Y) : SM X J K Y where
  Q := Unit
  start := ()
  table := fun _ reads top => .inl (f reads top)

def pure (y : Y) : SM X J K Y := peek (fun _ _ => y)

theorem exec_peek {f : Reads X J → (K → Option Bool) → Y}
    {i : Inputs X J} {s : Store J K} {B} (o : s.ok B) :
    (peek f).Exec i B s s (f (s.ro.see i) s.see) :=
  ⟨(), .stop o rfl⟩

theorem exec_pure {y : Y} {i : Inputs X J} {s : Store J K} {B} (o : s.ok B) :
    (pure y).Exec i B s s y := exec_peek o

/-- Read, carry out one stack/head transition, and return a label. -/
def act [Finite Y] (f : Reads X J → (K → Option Bool) → Y × StChange J K) :
    SM X J K Y where
  Q := Option Y
  start := none
  table := fun q reads top =>
    match q with
    | some y => .inl y
    | none =>
      let (y, c) := f reads top
      .inr (.withState c (some y))

theorem exec_act [Finite Y] {f : Reads X J → (K → Option Bool) → Y × StChange J K}
    {i : Inputs X J} {s : Store J K} {B y c} (e : f (s.ro.see i) s.see = (y,c))
    (o : s.ok B) (o' : (s.perform i c).ok B) :
    (act f).Exec i B s (s.perform i c) y := by
  refine ⟨some y, .step (s' := (some y, s.perform i c)) o ?_ (.stop o' rfl)⟩
  simp [step, act, e, SAction.withState]

def change (m : StChange J K) : SM X J K Unit := act fun _ _ => ((), m)

theorem exec_change {i : Inputs X J} {s : Store J K} {B} (m : StChange J K)
    (o : s.ok B) (o' : (s.perform i m).ok B) :
    (change m).Exec i B s (s.perform i m) () :=
  exec_act rfl o o'

section Bind
variable [Finite Y] (M : SM X J K Y) (N : Y → SM X J K Z)

def bind : SM X J K Z where
  Q := M.Q ⊕ (Σ y : Y, (N y).Q)
  start := .inl M.start
  table := fun q r t =>
    match q with
    | .inl q =>
      match M.table q r t with
      | .inl y => .inr (.none (.inr ⟨y, (N y).start⟩))
      | .inr c => .inr (.withState c.toStChange (.inl c.next))
    | .inr ⟨y, q⟩ =>
      match (N y).table q r t with
      | .inl z => .inl z
      | .inr c => .inr (.withState c.toStChange (.inr ⟨y,c.next⟩))

def bindFst (s : M.Cfg) : (M.bind N).Cfg := (Sum.inl s.1, s.2)
def bindSnd (y : Y) (s : (N y).Cfg) : (M.bind N).Cfg :=
  (Sum.inr (Sigma.mk y s.1), s.2)

theorem bind_stepFst (i : Inputs X J) (s : M.Cfg) :
    (M.bind N).step i (M.bindFst N s) =
      match M.step i s with
      | Sum.inl y => Sum.inr (M.bindSnd N y ((N y).start, s.2))
      | Sum.inr w => Sum.inr (M.bindFst N w) := by
  dsimp only [step, bind, bindFst, bindSnd]
  cases M.table s.1 (s.2.ro.see i) s.2.see <;> rfl

theorem bind_stepSnd (i : Inputs X J) (y : Y) (s : (N y).Cfg) :
    (M.bind N).step i (M.bindSnd N y s) =
      match (N y).step i s with
      | Sum.inl z => Sum.inl z
      | Sum.inr w => Sum.inr (M.bindSnd N y w) := by
  dsimp only [step, bind, bindSnd]
  cases (N y).table s.1 (s.2.ro.see i) s.2.see <;> rfl

theorem run_bindSnd {y : Y} {i : Inputs X J} {s t : (N y).Cfg} {B z}
    (e : (N y).Run i B s t z) :
    (M.bind N).Run i B (M.bindSnd N y s) (M.bindSnd N y t) z := by
  induction e with
  | stop o e => exact .stop o (by rw [bind_stepSnd, e])
  | step o e _ ih => exact .step o (by rw [bind_stepSnd, e]) ih

theorem run_bind {i : Inputs X J} {s t : M.Cfg} {B y z}
    (e : M.Run i B s t y) {u : (N y).Cfg}
    (e' : (N y).Run i B ((N y).start, t.2) u z) :
    (M.bind N).Run i B (M.bindFst N s) (M.bindSnd N y u) z := by
  induction e with
  | stop o e =>
    exact .step o (by rw [bind_stepFst, e]) (M.run_bindSnd N e')
  | step o e _ ih =>
    exact .step o (by rw [bind_stepFst, e]) (ih e')

theorem exec_bind {i : Inputs X J} {s t u : Store J K} {B y z}
    (e : M.Exec i B s t y) (e' : (N y).Exec i B t u z) :
    (M.bind N).Exec i B s u z := by
  obtain ⟨_, e⟩ := e
  obtain ⟨_, e'⟩ := e'
  exact ⟨_, M.run_bind N e e'⟩
end Bind

def seq (M : SM X J K Unit) (N : SM X J K Y) : SM X J K Y := M.bind fun _ => N
theorem exec_seq {i : Inputs X J} {s t u : Store J K} {B y}
    {M : SM X J K Unit} {N : SM X J K Y}
    (e : M.Exec i B s t ()) (e' : N.Exec i B t u y) :
    (M.seq N).Exec i B s u y :=
  M.exec_bind _ e e'

section Loop
variable (M : SM X J K (Option Y))
def loop : SM X J K Y where
  Q := M.Q
  start := M.start
  table := fun q r t =>
    match M.table q r t with
    | .inl none => .inr (.none M.start)
    | .inl (some y) => .inl y
    | .inr c => .inr c

/-- "Continue" label splices in a silent start move. -/
theorem loop_step (i : Inputs X J) (s : M.Cfg) :
    M.loop.step i s =
      match M.step i s with
      | Sum.inl none => Sum.inr (M.start, s.2)
      | Sum.inl (some y) => Sum.inl y
      | Sum.inr w => Sum.inr w := by
  dsimp only [loop, step]
  cases e : M.table s.1 (s.2.ro.see i) s.2.see with
  | inl v => cases v <;> rfl
  | inr w => rfl

-- Keep the label general through induction
theorem run_loop {i : Inputs X J} {s t w : M.Cfg} {B y v}
    (next : match v with
      | none => M.loop.Run i B (M.start, t.2) w y
      | some y' => y = y' ∧ t = w)
    (e : M.Run i B s t v) :
    M.loop.Run i B s w y := by
  induction e with
  | @stop t a o e =>
    cases a with
    | none => exact .step o (by rw [loop_step, e]) next
    | some a =>
      obtain ⟨rfl, rfl⟩ := (show y = a ∧ t = w from next)
      exact .stop o (by rw [loop_step, e])
  | step o e _ ih =>
    exact .step o (by rw [loop_step, e]) (ih next)

theorem loop_stop {i : Inputs X J} {s t : Store J K} {B y}
    (e : M.Exec i B s t (some y)) : M.loop.Exec i B s t y := by
  obtain ⟨q, e⟩ := e
  exact ⟨q, M.run_loop (v := some y) (And.intro rfl rfl) e⟩

theorem loop_continue {i : Inputs X J} {s t u : Store J K} {B y}
    (e : M.Exec i B s t none)
    (r : M.loop.Exec i B t u y) : M.loop.Exec i B s u y := by
  obtain ⟨q, e⟩ := e
  obtain ⟨v, r⟩ := r
  exact ⟨v, M.run_loop (t := (q, t)) (v := none) r e⟩
end Loop
end Fifths.SM

end OAI
