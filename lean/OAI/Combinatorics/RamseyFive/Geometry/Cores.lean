import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ReverseMiss
import OAI.Combinatorics.RamseyFive.Geometry.CoreGeometry

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.LowConflict
open scoped BigOperators Classical
noncomputable section
variable {K V α β : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype α] [Fintype β]

def firstCore (p : Law (α × β)) (w : β → Module.Dual K V) (a : α) :
    Submodule K (Module.Dual K V) := core (fiber p a) w (1/200)

def secondCore (p : Law (α × β)) (v : α → V) (b : β) : Submodule K V :=
  core (fiber (swap p) b) v (1/200)

lemma conditional_flag_annihilation (p : Law (α × β)) (v : α → V)
    (w : β → Module.Dual K V) (hflag : ∀ a b, 0<p (a,b) → w b (v a)=0)
    (a : α) (ha : 0<first p a) :
    failure (fiber p a) w (Module.Dual.eval K V (v a)) = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  change (if w b (v a) ≠ 0 then fiber p a b else 0)=0
  split_ifs with h
  · by_contra hz
    have hp : 0 < p (a,b) := by
      rw [mass_eq_first_mul_fiber]
      exact mul_pos ha (lt_of_le_of_ne ((fiber p a).nonneg b) (Ne.symm hz))
    exact h (hflag a b hp)
  · rfl

lemma firstCore_self (p : Law (α × β)) (v : α → V)
    (w : β → Module.Dual K V) (hflag : ∀ a b, 0<p (a,b) → w b (v a)=0)
    (a : α) (ha : 0<first p a) : v a ∈ (firstCore p w a).dualCoannihilator := by
  apply (Submodule.mem_dualCoannihilator _).mpr
  intro f hf
  exact (mem_core _ _ _ f).mp hf (Module.Dual.eval K V (v a))
    (by rw [conditional_flag_annihilation p v w hflag a ha]; norm_num)

lemma secondCore_self (p : Law (α × β)) (v : α → V)
    (w : β → Module.Dual K V) (hflag : ∀ a b, 0<p (a,b) → w b (v a)=0)
    (b : β) (hb : 0<second p b) : w b ∈ (secondCore (K := K) p v b).dualAnnihilator := by
  have hz : failure (fiber (swap p) b) v (w b)=0 := by
    apply Finset.sum_eq_zero
    intro a _
    change (if w b (v a)≠0 then fiber (swap p) b a else 0)=0
    split_ifs with h
    · by_contra hn
      have hp : 0 < p (a,b) := by
        rw [mass_eq_second_mul_fiber]
        exact mul_pos hb (lt_of_le_of_ne ((fiber (swap p) b).nonneg a) (Ne.symm hn))
      exact h (hflag a b hp)
    · rfl
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro z hz'
  exact (mem_core _ _ _ z).mp hz' (w b) (by rw [hz]; norm_num)

variable [FiniteDimensional K V]

theorem actual_integer_rectangle (hdim : finrank K V=5) (r : ℕ) (hr : r≤5)
    (p q : Law (α × β)) (v : α → V) (w : β → Module.Dual K V)
    (hp : ∀ a b, 0<p (a,b) → w b (v a)=0)
    (hq : ∀ a b, 0<q (a,b) → w b (v a)=0)
    (good : α → β → Prop)
    (hg : ∀ a y, good a y → 0<first p a ∧ 0<second q y)
    (hU : ∀ a y, good a y → r ≤ finrank K (firstCore p w a))
    (hW : ∀ a y, good a y → 5-r ≤ finrank K (secondCore (K := K) q v y))
    (a c : α) (b y : β) (h : capturedEvent p q w v good a b c y) :
    InRectangle (firstCore p w a) (v a) (w b) ∧
      InRectangle (firstCore p w a) (v c) (w y) := by
  exact integer_band_rectangle hdim r _ _ (hU a y h.1) (hW a y h.1) hr
    (captured_orthogonal p q w v good a b c y h) _ _ _ _
    (firstCore_self p v w hp a (hg a y h.1).1) h.2.2.1 h.2.2.2
    (secondCore_self q v w hq y (hg a y h.1).2)

theorem actual_high_rectangles (hdim : finrank K V=5)
    (p q : Law (α × β)) (v : α → V) (w : β → Module.Dual K V)
    (hp : ∀ a b, 0<p (a,b) → w b (v a)=0)
    (hq : ∀ a b, 0<q (a,b) → w b (v a)=0)
    (good : α → β → Prop)
    (hg : ∀ a y, good a y → 0<first p a ∧ 0<second q y ∧ w y (v a)=0)
    (hU : ∀ a y, good a y → 2 ≤ finrank K (firstCore p w a))
    (hW : ∀ a y, good a y → 2 ≤ finrank K (secondCore (K := K) q v y))
    (a c : α) (b y : β) (h : capturedEvent p q w v good a b c y) :
    (InRectangle (firstCore p w a) (v a) (w b) ∧
      InRectangle (firstCore p w a) (v c) (w y)) ∨
    (InRectangle (secondCore (K := K) q v y).dualAnnihilator (v a) (w b) ∧
      InRectangle (secondCore (K := K) q v y).dualAnnihilator (v c) (w y)) := by
  exact high_band_rectangles hdim _ _ (hU a y h.1) (hW a y h.1)
    (captured_orthogonal p q w v good a b c y h) _ _ _ _
    (firstCore_self p v w hp a (hg a y h.1).1) h.2.2.1 h.2.2.2
    (secondCore_self q v w hq y (hg a y h.1).2.1) (hg a y h.1).2.2

theorem actual_open_impossible (hdim : finrank K V=5) (r : ℕ) (hr : r≤6)
    (p q : Law (α × β)) (v : α → V) (w : β → Module.Dual K V)
    (good : α → β → Prop)
    (hU : ∀ a y, good a y → r ≤ finrank K (firstCore p w a))
    (hW : ∀ a y, good a y → 6-r ≤ finrank K (secondCore (K := K) q v y))
    (a c : α) (b y : β) : ¬capturedEvent p q w v good a b c y := by
  intro h
  exact open_band_impossible hdim r _ _ (hU a y h.1) (hW a y h.1) hr
    (captured_orthogonal p q w v good a b c y h)
end
end SharpRamseyFive.CoreGeometry

end OAI
