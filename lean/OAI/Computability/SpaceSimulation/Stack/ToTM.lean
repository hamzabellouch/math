import OAI.Computability.SpaceSimulation.StackMachine

namespace OAI

/-! Compilation of stack space-bounded algorithms to Turing machines. -/
namespace Fifths

namespace Tape
def packStack : List Bool → Tape (Option Bool)
  | [] => init none
  | b :: l =>
    let t := packStack l
    ⟨t.pos + 1, Function.update t.sym (t.pos + 1) (some b)⟩

@[simp] theorem packStack_see (l : List Bool) : (packStack l).see = l.head? := by
  cases l <;> simp [packStack, see, init]
theorem packStack_pos (l : List Bool) : (packStack l).pos = (l.length : ℤ) := by
  induction l <;> simp [packStack, init, *]
theorem packStack_over (l : List Bool) (p : ℤ) (h : (packStack l).pos < p) :
    (packStack l).sym p = none := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    dsimp only [packStack] at h ⊢
    rw [Function.update_of_ne (ne_of_gt h)]
    apply ih; omega

end Tape

namespace StOp
abbrev Cell := Option Bool

/-- Empty has its head on a blank. All other heads read the top. -/
def first (o : StOp) (r : Cell) : WriteMove Cell := match o with
  | keep => ⟨r,.N⟩
  | push _ => ⟨r,.R⟩
  | pop => ⟨none, if r.isSome then .L else .N⟩

def second (o : StOp) (r : Cell) : WriteMove Cell :=
  ⟨match o with | push b => some b | _ => r, .N⟩

def middle (l : List Bool) (o : StOp) : Tape Cell :=
  (Tape.packStack l).perform (o.first l.head?)

theorem middle_pos (l : List Bool) (o : StOp) :
    (middle l o).pos = ((o.apply l).length : ℤ) := by
  cases o <;> cases l <;>
    simp [middle, first, Tape.perform, Tape.packStack_pos, apply]

theorem second_middle (l : List Bool) (o : StOp) :
    (middle l o).perform (o.second (middle l o).see) =
      Tape.packStack (o.apply l) := by
  open Tape in
  have hs (t : Tape Cell) :
      t.perform ⟨t.see, .N⟩ = t := by simp [perform, see]
  cases o with
  | keep =>
    change (middle l _).perform ⟨_, .N⟩ = Tape.packStack l
    rw [hs]
    unfold middle
    rw [← Tape.packStack_see]
    exact hs _
  | push b =>
    unfold middle
    rw [← Tape.packStack_see]
    simp only [first, Tape.see, second, Tape.perform, Dir.delta, Function.update_eq_self,
      add_zero, apply, Tape.packStack]
  | pop =>
    change (middle l _).perform ⟨_, .N⟩ = _
    rw [hs]
    cases l with
    | nil =>
      change (Tape.packStack []).perform ⟨(Tape.packStack []).see, .N⟩ = _
      exact hs _
    | cons b l =>
      have h := Tape.packStack_over l ((Tape.packStack l).pos + 1) (by omega)
      simp [middle, Tape.packStack, Tape.perform, first, apply, ← h]

end StOp

namespace SM
variable {X J K Y : Type} [Fintype K] (M : SM X J K Y)

def toTM : TM X J Y where
  Q := M.Q ⊕ M.Q × (K → StOp)
  K := K
  W := fun _ => StOp.Cell
  blank := fun _ => none
  start := Sum.inl M.start
  table := fun q r t =>
    match q with
    | .inl q =>
      match M.table q r t with
      | .inl y => .inl y
      | .inr c => .inr
        ⟨Sum.inr (c.next, c.ops), c.advance, fun k => StOp.first (c.ops k) (t k)⟩
    | .inr (q, ops) => .inr ⟨.inl q, {}, fun k => StOp.second (ops k) (t k)⟩

def encoded (s : M.Cfg) : M.toTM.Cfg :=
  ⟨Sum.inl s.1, s.2.ro, fun k => Tape.packStack (s.2.st k)⟩

def midCfg (i : Inputs X J) (s : M.Cfg) (a : SAction M.Q J K) : M.toTM.Cfg :=
  ⟨Sum.inr (a.next, a.ops), s.2.ro.walk i a.advance,
   fun k => StOp.middle (s.2.st k) (a.ops k)⟩

def window (B : ℕ) : M.toTM.Window :=
  ⟨fun _ => 0, fun _ => B⟩

theorem toTM_step (i : Inputs X J) (w : M.Cfg) :
    M.toTM.step i (M.encoded w) =
      match M.table w.1 (w.2.ro.see i) w.2.see with
      | Sum.inl y => Sum.inl y
      | Sum.inr a => Sum.inr (M.midCfg i w a) := by
  dsimp only [TM.step, toTM, encoded]
  have h : (fun k => (Tape.packStack (w.2.st k)).see) = w.2.see := by
    ext; simp [Store.see]
  rw [h]
  cases M.table w.1 (w.2.ro.see i) w.2.see with
  | inl => rfl
  | inr c =>
    simp [midCfg, StOp.middle]
    rfl

theorem toTM_mid (i : Inputs X J) (s : M.Cfg) (a : SAction M.Q J K) :
    M.toTM.step i (M.midCfg i s a) =
      Sum.inr (M.encoded (a.next, s.2.perform i a.toStChange)) := by
  simp only [TM.step, midCfg, toTM, encoded, Readers.stationary, Store.perform,
    StOp.second_middle]

theorem encoded_ok {s : M.Cfg} {B} (o : s.2.ok B) : (M.window B).ok (M.encoded s) := by
  intro k
  change -(0 : ℤ) ≤ (Tape.packStack _).pos ∧ (Tape.packStack (s.2.st k)).pos ≤ B
  simp [Tape.packStack_pos, o k]

theorem mid_ok {s : M.Cfg} {i : Inputs X J} {a : SAction M.Q J K} {B}
    (o : (s.2.perform i a.toStChange).ok B) :
    (M.window B).ok (M.midCfg i s a) := by
  intro k
  change -(0 : ℤ) ≤ (StOp.middle _ _).pos ∧
    (StOp.middle (s.2.st k) (a.ops k)).pos ≤ B
  simp only [StOp.middle_pos]
  have h : ((a.ops k).apply (s.2.st k)).length ≤ B := o k
  omega

theorem toTM_run {i : Inputs X J} {B} {s t : M.Cfg} {y}
    (e : M.Run i B s t y) :
    Runs (M.toTM.step i) (M.window B).ok (M.encoded s) (M.encoded t) y := by
  induction e with
  | @stop s y o eqn =>
    apply Runs.stop (M.encoded_ok o)
    unfold step at eqn
    cases h : M.table s.1 (s.2.ro.see i) s.2.see with
    | inl => rw [toTM_step, h]; simpa [h] using eqn
    | inr => rw [h] at eqn; contradiction
  | @step s w t y o eqn tail ih =>
    unfold step at eqn
    cases h : M.table s.1 (s.2.ro.see i) s.2.see with
    | inl => rw [h] at eqn; contradiction
    | inr a =>
      simp only [h, Sum.inr.injEq] at eqn
      subst w
      exact .step (M.encoded_ok o) (by rw [toTM_step, h])
        (.step (M.mid_ok tail.startOk) (M.toTM_mid i s a) ih)

def multiplier : ℕ :=
  ∑ k : M.toTM.K, M.toTM.width k

theorem window_bits (B) : (M.window B).bits = M.multiplier * (B+1) := by
  simp only [TM.Window.bits, window, zero_add, multiplier, Finset.sum_mul]; ac_rfl
theorem toTM_within {i : Inputs X J} {B} {t : Store J K} {y}
    (e : M.Exec i B (.init (fun _ => [])) t y) :
    M.toTM.Within i y (M.multiplier * (B+1)) := by
  obtain ⟨q,e⟩ := e
  exact ⟨M.window B, le_of_eq (M.window_bits B), _, M.toTM_run e⟩

end SM
end Fifths

end OAI
