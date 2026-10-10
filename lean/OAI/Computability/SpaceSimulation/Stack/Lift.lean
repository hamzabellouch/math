import OAI.Computability.SpaceSimulation.StackMachine

namespace OAI

/-! Renamings / framing extra stacks, and presence of extra RO arguments. -/

namespace Fifths
variable {X J K L Y : Type}
namespace StChange
noncomputable def pad (e : K ↪ L) (s : StChange J K) : StChange J L :=
  ⟨s.advance, Function.extend e s.ops (fun _ => .keep)⟩
end StChange

namespace Store
noncomputable def pad (e : K ↪ L) (d : L → List Bool) (s : Store J K) : Store J L :=
  ⟨s.ro, Function.extend e s.st d⟩

@[simp] theorem pad_st (e : K ↪ L) (d) (s : Store J K) (k) :
    (s.pad e d).st (e k) = s.st k :=
  e.injective.extend_apply ..
theorem pad_st' (e : K ↪ L) (d) (s : Store J K) (l)
    (h : ¬∃ k, e k = l) : (s.pad e d).st l = d l :=
  Function.extend_apply' _ _ _ h

theorem pad_perform (e : K ↪ L) (d) (s : Store J K) (i : Inputs X J)
    (m : StChange J K) :
    (s.pad e d).perform i (m.pad e) = (s.perform i m).pad e d := by
  classical
  dsimp only [pad, perform, StChange.pad]
  congr 1
  funext l
  by_cases h : ∃ k, e k = l
  · obtain ⟨k,rfl⟩ := h
    rw [e.injective.extend_apply, e.injective.extend_apply, e.injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ h,
        Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
    rfl
theorem pad_ok {e : K ↪ L} {d} {s : Store J K} {B} (o : s.ok B)
    (p : ∀ l : L, (d l).length ≤ B) : (s.pad e d).ok B := by
  classical
  intro l
  by_cases h : ∃ k, e k = l
  · obtain ⟨k,rfl⟩ := h
    rw [pad_st]; exact o k
  · rw [pad_st' _ _ _ _ h]; exact p l
end Store

namespace SM
section Pads
variable (M : SM X J K Y) (e : K ↪ L)

noncomputable def pad : SM X J L Y where
  Q := M.Q
  start := M.start
  table := fun q r t =>
    match M.table q r (t ∘ e) with
    | .inl y => .inl y
    | .inr c => .inr (.withState (c.toStChange.pad e) c.next)

noncomputable def padCfg (d : L → List Bool) (w : M.Cfg) : (M.pad e).Cfg :=
  (w.1, w.2.pad e d)

theorem pad_step (i : Inputs X J) (w : M.Cfg) (d : L → List Bool) :
    (M.pad e).step i (M.padCfg e d w) =
      match M.step i w with
      | Sum.inl y => Sum.inl y
      | Sum.inr s => Sum.inr (M.padCfg e d s) := by
  dsimp only [step, padCfg, pad]
  have a : (w.2.pad e d).ro = w.2.ro := rfl
  have b : (w.2.pad e d).see ∘ e = w.2.see := by
    funext k; simp [Store.see]
  rw [a,b]
  cases M.table w.1 (w.2.ro.see i) w.2.see with
  | inl => rfl
  | inr => simp only [SAction.withState, Store.pad_perform]

theorem pad_run {d : L → List Bool} {i : Inputs X J} {s t : M.Cfg} {B y}
    (r : M.Run i B s t y) (p : ∀ l : L, (d l).length ≤ B) :
    (M.pad e).Run i B (M.padCfg e d s) (M.padCfg e d t) y := by
  induction r with
  | stop o a => exact .stop (Store.pad_ok o p) (by rw [pad_step, a])
  | step o a _ ih => exact .step (Store.pad_ok o p) (by rw [pad_step, a]) ih

theorem pad_exec {d : L → List Bool} {i : Inputs X J} {s t : Store J K} {B y}
    (r : M.Exec i B s t y) (p : ∀ l : L, (d l).length ≤ B) :
    (M.pad e).Exec i B (s.pad e d) (t.pad e d) y := by
  obtain ⟨q,r⟩ := r
  exact ⟨q, M.pad_run e r p⟩
end Pads

section Args
variable (M : SM X Empty K Y)

/-- Preserve a program that never reads any arg tapes. -/
def withArgs (J : Type) : SM X J K Y where
  Q := M.Q
  start := M.start
  table := fun q r t =>
    match M.table q ⟨r.sx, Empty.elim⟩ t with
    | .inl y => .inl y
    | .inr c => .inr (.withState ⟨{dx := c.advance.dx}, c.ops⟩ c.next)

def storeArgs {J : Type} (p : J → ℕ) (s : Store Empty K) : Store J K :=
  ⟨⟨s.ro.px,p⟩, s.st⟩

def argsCfg {J : Type} (p : J → ℕ) (s : M.Cfg) : (M.withArgs J).Cfg :=
  (s.1, storeArgs p s.2)

theorem args_step (i : Inputs X J) (w : M.Cfg) (p : J → ℕ) :
    (M.withArgs J).step i (M.argsCfg p w) =
      match M.step ⟨i.publicWord, Empty.elim⟩ w with
      | Sum.inl y => Sum.inl y
      | Sum.inr s => Sum.inr (M.argsCfg p s) := by
  dsimp only [step, argsCfg, withArgs]
  have a :
      (Reads.mk ((storeArgs p w.2).ro.see i).sx Empty.elim : Reads X Empty) =
        w.2.ro.see ⟨i.publicWord, Empty.elim⟩ := by
    dsimp only [Readers.see, storeArgs]
    congr
    exact Subsingleton.elim _ _
  rw [a, show (storeArgs p w.2).see = w.2.see from rfl]
  cases M.table w.1 (w.2.ro.see ⟨i.publicWord, Empty.elim⟩) w.2.see <;> rfl

theorem args_exec {i : Inputs X J} {s t : Store Empty K} {B y}
    (p : J → ℕ) (r : M.Exec ⟨i.publicWord, Empty.elim⟩ B s t y) :
    (M.withArgs J).Exec i B (storeArgs p s) (storeArgs p t) y := by
  have h : ∀ y v w, M.Run ⟨i.publicWord, Empty.elim⟩ B v w y →
      (M.withArgs J).Run i B (M.argsCfg p v) (M.argsCfg p w) y := by
    intro y v w r
    induction r with
    | stop o a => exact .stop o (by rw [args_step, a])
    | step o a _ ih => exact .step o (by rw [args_step, a]) ih
  obtain ⟨q,r⟩ := r
  exact ⟨q, h _ _ _ r⟩
end Args
end SM
end Fifths

end OAI
