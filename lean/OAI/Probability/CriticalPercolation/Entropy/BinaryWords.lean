import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryLaw

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

def sides : (n : ℕ) → History E n → Fin n → Bool
  | 0, _ => Fin.elim0
  | n+1, h => Fin.snoc (sides n h.1) h.2.1

def marks : (n : ℕ) → History E n → Fin n → Option E
  | 0, _ => Fin.elim0
  | n+1, h => Fin.snoc (marks n h.1) h.2.2

def fromWords : (n : ℕ) → (Fin n → Bool) → (Fin n → Option E) → History E n
  | 0, _, _ => PUnit.unit
  | n+1, b, m => (fromWords n (Fin.init b) (Fin.init m),b (Fin.last n),m (Fin.last n))

lemma fromWords_sides_marks (n : ℕ) (h : History E n) :
    fromWords n (sides n h) (marks n h) = h := by
  induction n with
  | zero => cases h; rfl
  | succ n ih =>
    simp only [fromWords,sides,marks,Fin.init_snoc,Fin.snoc_last,ih]
    rfl

lemma sides_fromWords (n : ℕ) (b : Fin n → Bool) (m : Fin n → Option E) :
    sides n (fromWords n b m) = b := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih => simp only [fromWords,sides,ih,Fin.snoc_init_self]

lemma marks_fromWords (n : ℕ) (b : Fin n → Bool) (m : Fin n → Option E) :
    marks n (fromWords n b m) = m := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih => simp only [fromWords,marks,ih,Fin.snoc_init_self]

def wordsEquiv (n : ℕ) : History E n ≃ (Fin n → Bool) × (Fin n → Option E) where
  toFun h := (sides n h, marks n h)
  invFun h := fromWords n h.1 h.2
  left_inv := fromWords_sides_marks n
  right_inv := fun h => Prod.ext (sides_fromWords n h.1 h.2) (marks_fromWords n h.1 h.2)

lemma interval_fromWords (d n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E) :
    interval d n (fromWords n b m) = interval d n (fromWords n b m') := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fromWords,interval,ih (Fin.init b) (Fin.init m) (Fin.init m')]

lemma nextIndex_fromWords (d n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E) :
    nextIndex d n (fromWords n b m) = nextIndex d n (fromWords n b m') := by
  simp only [nextIndex,interval_fromWords d n b m m']

lemma anchors_fromWords (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (m m' : Fin n → Option E) :
    anchors d x n (fromWords n b m) = anchors d x n (fromWords n b m') := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fromWords,anchors,ih (Fin.init b) (Fin.init m) (Fin.init m'),
      nextIndex_fromWords d n (Fin.init b) (Fin.init m) (Fin.init m')]

lemma anchorSet_fromWords (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (m m' : Fin n → Option E) :
    anchorSet d x n (fromWords n b m) = anchorSet d x n (fromWords n b m') := by
  simp only [anchorSet,anchors_fromWords d x n b m m']

def historyPrefix : (n : ℕ) → History E n → (k : ℕ) → History E k
  | 0, _, 0 => PUnit.unit
  | 0, _, k+1 => fromWords (k+1) (fun _ => true) (fun _ => none)
  | n+1, h, k => if he : k = n+1 then he.symm ▸ h else historyPrefix n h.1 k

lemma prefix_self (n : ℕ) (h : History E n) : historyPrefix n h n = h := by
  cases n with
  | zero => cases h; rfl
  | succ n => simp only [historyPrefix,dite_true]

lemma prefix_prev (n : ℕ) (h : History E (n+1)) (k : ℕ) (hk : k ≤ n) :
    historyPrefix (n+1) h k = historyPrefix n h.1 k := by
  rw [historyPrefix,dite_eq_right (by omega : k ≠ n+1)]

lemma prefix_last (n : ℕ) (h : History E (n+1)) : historyPrefix (n+1) h n = h.1 := by
  rw [prefix_prev _ _ _ le_rfl,prefix_self]

lemma prefix_fromWords (n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E)
    (k : ℕ) (hk : k ≤ n) :
    sides k (historyPrefix n (fromWords n b m) k) = sides k (historyPrefix n (fromWords n b m') k) := by
  induction n with
  | zero =>
    have he : k=0 := by omega
    subst k
    exact Subsingleton.elim _ _
  | succ n ih =>
    by_cases he : k=n+1
    · subst k
      simp only [prefix_self,sides_fromWords]
    · have hk' : k ≤ n := by omega
      rw [prefix_prev _ _ _ hk',prefix_prev _ _ _ hk']
      exact ih (Fin.init b) (Fin.init m) (Fin.init m') hk'

lemma anchors_sides (d : ℕ) (x : ℕ → V) (n : ℕ) (h h' : History E n)
    (hs : sides n h = sides n h') : anchors d x n h = anchors d x n h' := by
  conv_lhs => rw [←fromWords_sides_marks n h]
  conv_rhs => rw [←fromWords_sides_marks n h']
  rw [hs]
  exact anchors_fromWords d x n _ _ _

lemma interval_sides (d n : ℕ) (h h' : History E n) (hs : sides n h = sides n h') :
    interval d n h = interval d n h' := by
  conv_lhs => rw [←fromWords_sides_marks n h]
  conv_rhs => rw [←fromWords_sides_marks n h']
  rw [hs]
  exact interval_fromWords d n _ _ _

lemma nextIndex_sides (d n : ℕ) (h h' : History E n) (hs : sides n h = sides n h') :
    nextIndex d n h = nextIndex d n h' := by
  simp only [nextIndex,interval_sides d n h h' hs]

section Density
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma density_prefix_support (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) (k : ℕ) (hk : k ≤ n) :
    density G order d x p w r₀ k (historyPrefix n h k) ω ≠ 0 := by
  induction n with
  | zero =>
    have he : k=0 := by omega
    subst k
    simpa only [prefix_self] using hr
  | succ n ih =>
    by_cases he : k=n+1
    · subst k
      simpa only [prefix_self] using hr
    · have hk' : k ≤ n := by omega
      rw [prefix_prev _ _ _ hk']
      exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1 hk'

end Density
end CriticalPercolation.BinaryLaw
end
end

end OAI
