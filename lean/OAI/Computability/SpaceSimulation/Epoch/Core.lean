import OAI.Computability.SpaceSimulation.Register.Digits

namespace OAI

namespace Fifths
namespace Radix

theorem join_lt {m n a u v : ℕ} (hu : u < m^n) (hv : v < m^a) :
    u + m^n*v < m^(n+a) := by
  rw [pow_add]
  calc
    _ < m^n + m^n*v := by omega
    _ = m^n*(v+1) := by ring
    _ ≤ _ := by gcongr; omega

theorem pack_append (m n a : ℕ) (f : ℕ → ℕ) :
    pack m f (n+a) = pack m f n + m^n * pack m (fun i => f (n+i)) a := by
  induction a with
  | zero => simp [pack]
  | succ k ih =>
    rw [← Nat.add_assoc,pack,ih,pack,pow_add]
    ring

-- Needed to fix first digit pasting a suffix.
theorem get_join_zero (m n u v : ℕ) (h : 0 < n) :
    get m (u + m^n*v) 0 = get m u 0 := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [get_zero,pow_succ',mul_assoc]
    simp
end Radix

/-- A deterministic reference visit touches one selected block. All
bounded state carried between visits, other than the blocks, is a
raw c-bit controller. `k>0`, `b=k*k`; block tapings have at most
b controller-width digits. -/
structure Tour where
  k : ℕ
  c : ℕ
  N : ℕ
  pk : 0 < k
  blocks : 0 < N
  init : ℕ
  tape : ℕ → ℕ
  sel : ℕ → ℕ
  visit : ℕ → ℕ → ℕ × ℕ
  rangeSel : ∀ z, sel z < N

structure Scene where
  ctrl : ℕ
  cells : ℕ → ℕ

namespace Tour
open Radix

variable (D : Tour)
def b := D.k*D.k
def E := D.k+1
def m := 2^D.c
def width := D.c*(D.b+1)
def guessLength := D.c*D.k

theorem m_pos : 0 < D.m := by unfold m; positivity
theorem powers (n : ℕ) : 2^(D.c*n) = D.m^n := by rw [pow_mul]; rfl
theorem b_pos : 0 < D.b := Nat.mul_pos D.pk D.pk
theorem k_le : D.k ≤ D.b := Nat.le_mul_of_pos_right _ D.pk

def step (s : Scene) : Scene :=
  let i := D.sel s.ctrl
  let (c,b) := D.visit s.ctrl (s.cells i)
  ⟨c, Function.update s.cells i b⟩
def story (D : Tour) : ℕ → Scene
  | 0 => ⟨D.init,D.tape⟩
  | n+1 => D.step (D.story n)

structure FiniteWords : Prop where
  init : D.init < D.m
  tape : ∀ i, D.tape i < D.m^D.b
  visit : ∀ z B, z < D.m → B < D.m^D.b →
    (D.visit z B).1 < D.m ∧ (D.visit z B).2 < D.m^D.b

theorem ctrl_step (s : Scene) :
    (D.step s).ctrl = (D.visit s.ctrl (s.cells (D.sel s.ctrl))).1 := rfl
theorem cells_step (s : Scene) (j) :
    (D.step s).cells j =
      if D.sel s.ctrl = j then (D.visit s.ctrl (s.cells j)).2 else s.cells j := by
  by_cases h : D.sel s.ctrl = j
  · simp [step,h]
  · simp [step,h,Ne.symm h]
theorem finite_story (g : D.FiniteWords) (n : ℕ) :
    (D.story n).ctrl < D.m ∧ ∀ i, (D.story n).cells i < D.m^D.b := by
  induction n with
  | zero => exact ⟨g.init,g.tape⟩
  | succ n ih =>
    rw [story]
    refine ⟨(g.visit _ _ ih.1 (ih.2 _)).1, fun i => ?_⟩
    rw [cells_step]
    split
    · exact (g.visit _ _ ih.1 (ih.2 _)).2
    · exact ih.2 i

/-- Proposed transcript Z has controller at each digit. Scan local
block i from block data B. Continue applying the visits even on a
failed test. Normalize initial B (no-op on semantic arguments). -/
def replayStep (i Z j : ℕ) (s : ℕ × Bool) : ℕ × Bool :=
  let d := get D.m Z j
  if D.sel d = i then
    let t := D.visit d s.1
    (t.2,s.2 && decide (t.1 = get D.m Z (j+1)))
  else s

def replay (D : Tour) (i Z B : ℕ) : ℕ → ℕ × Bool
  | 0 => (B % D.m^D.b,true)
  | n+1 => D.replayStep i Z n (D.replay i Z B n)

theorem replay_lt (g : D.FiniteWords) (i Z B n : ℕ) :
    (D.replay i Z B n).1 < D.m^D.b := by
  induction n with
  | zero =>
    apply Nat.mod_lt
    exact pow_pos D.m_pos _
  | succ n ih =>
    simp only [replay,replayStep]
    split
    · exact (g.visit _ _ (get_lt D.m_pos _ _) ih).2
    · exact ih

/-- Offered replay from step t. Predicates need only check
each block separately. -/
def agrees (Z t n : ℕ) : Prop :=
  ∀ j ≤ n, get D.m Z j = (D.story (t+j)).ctrl

def replayOn (i Z t n : ℕ) := D.replay i Z ((D.story t).cells i) n

theorem replay_true (g : D.FiniteWords) {Z t} (n) (h : D.agrees Z t n) (i) :
    D.replayOn i Z t n = ((D.story (t+n)).cells i,true) := by
  induction n with
  | zero =>
    simp [replayOn,replay,Nat.mod_eq_of_lt ((D.finite_story g t).2 i)]
  | succ n ih =>
    have H : D.replayOn i Z t n = ((D.story (t+n)).cells i,true) :=
      ih fun j l => h j (by omega)
    unfold replayOn at *
    rw [replay,H]
    simp only [replayStep,h n (by omega), h (n+1) (by omega),
      story,cells_step,ctrl_step]
    split <;> rename_i e
    · simp [e]
    · simp [e]

theorem passes_agree (g : D.FiniteWords) {Z t n} (q : get D.m Z 0 = (D.story t).ctrl)
    (h : ∀ i < D.N, (D.replayOn i Z t n).2 = true) : D.agrees Z t n := by
  induction n with
  | zero =>
    intro j l
    have : j=0 := by omega
    subst j; simpa using q
  | succ n ih =>
    have f : D.agrees Z t n := by
      refine ih fun i r => ?_
      have e := h i r
      simp only [replayOn,replay,replayStep] at e
      split at e <;> rename_i l
      · exact ((Bool.and_eq_true ..).mp e).1
      · exact e
    intro j r
    by_cases e : j≤n
    · exact f j e
    rw [show j=n+1 by omega,← Nat.add_assoc,story,ctrl_step]
    let c := get D.m Z n
    let i := D.sel c
    have y := h i (D.rangeSel c)
    have m := D.replay_true g n f i
    have l : D.replay i Z ((D.story t).cells i) n = _ := m
    unfold replayOn at y
    rw [replay, l] at y
    have b : (D.visit c ((D.story (t+n)).cells i)).1 = get D.m Z (n+1) := by
      simpa [replayStep,i,c] using y
    rw [← f n le_rfl]
    exact b.symm

/-- Epoch prefix history stores n+1 controllers beginning at
visit-number t. -/
def log (t n : ℕ) : ℕ :=
  pack D.m (fun i => (D.story (t+i)).ctrl) (n+1)
theorem log_lt (g : D.FiniteWords) (t n) : D.log t n < D.m^(n+1) :=
  pack_lt D.m_pos _ _ (fun _i _ => (D.finite_story g _).1)
theorem log_agrees (g : D.FiniteWords) (t n) : D.agrees (D.log t n) t n :=
  fun _i h => get_pack D.m_pos _ _ (fun _i _ => (D.finite_story g _).1)
    (Nat.lt_succ_of_le h)
theorem agrees_log (g : D.FiniteWords) {Z t n} (h : Z < D.m^(n+1))
    (o : D.agrees Z t n) : D.log t n = Z := by
  refine Radix.ext D.m_pos (D.log_lt g _ _) h (fun i p => ?_)
  rw [D.log_agrees g t n i (by omega), o i (by omega)]

def suffix (t n : ℕ) : ℕ :=
  pack D.m (fun i => (D.story (t+(n+1+i))).ctrl) D.k
theorem suffix_lt (g : D.FiniteWords) (t n) :
    D.suffix t n < D.m^D.k :=
  pack_lt D.m_pos _ _ (fun _i _ => (D.finite_story g _).1)
theorem log_extend (t n : ℕ) :
    D.log t (n+D.k) = D.log t n + D.m^(n+1) * D.suffix t n := by
  unfold log suffix
  rw [show n+D.k+1 = n+1+D.k by omega,pack_append]
end Tour
end Fifths

end OAI
