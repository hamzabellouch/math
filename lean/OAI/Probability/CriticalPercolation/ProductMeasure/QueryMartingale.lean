import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.ClosedFresh

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*}

def queryCount : SearchTree E R → (E → Prop) → ℕ
  | .done _, _ => 0
  | .ask e l r, ω => 1 + if ω e then queryCount r ω else queryCount l ω

def centeredSum (p : ℝ) : SearchTree E R → (E → Prop) → ℝ
  | .done _, _ => 0
  | .ask e l r, ω => if ω e then (1-p)+centeredSum p r ω else -p+centeredSum p l ω

def truncate : SearchTree E R → ℕ → SearchTree E Unit
  | _, 0 => .done ()
  | .done _, _+1 => .done ()
  | .ask e l r, n+1 => .ask e (truncate l n) (truncate r n)

lemma truncate_valid [DecidableEq E] (t : SearchTree E R) (n : ℕ) (used : Finset E)
    (h : t.Valid used) : (t.truncate n).Valid used := by
  induction n generalizing t used with
  | zero => simp [truncate,Valid]
  | succ n ih =>
    cases t with
    | done r => trivial
    | ask e l r => exact ⟨h.1, ih l _ h.2.1, ih r _ h.2.2⟩

lemma queryCount_truncate_le (t : SearchTree E R) (n : ℕ) (ω : E → Prop) :
    (t.truncate n).queryCount ω ≤ n := by
  induction n generalizing t with
  | zero => simp [truncate,queryCount]
  | succ n ih =>
    cases t with
    | done r => simp [truncate,queryCount]
    | ask e l r =>
      simp only [truncate,queryCount]
      split_ifs <;> have := ih r <;> have := ih l <;> omega

lemma centeredSum_truncate_eq (t : SearchTree E R) (n : ℕ) (ω : E → Prop)
    (h : t.queryCount ω ≤ n) (p : ℝ) :
    (t.truncate n).centeredSum p ω = t.centeredSum p ω := by
  induction n generalizing t with
  | zero =>
    cases t with
    | done r => rfl
    | ask e l r => simp [queryCount] at h
  | succ n ih =>
    cases t with
    | done r => rfl
    | ask e l r =>
      by_cases he : ω e
      · simp only [queryCount,ite_eq_left he] at h
        simp only [truncate,centeredSum,ite_eq_left he]
        rw [ih r (by omega)]
      · simp only [queryCount,ite_eq_right he] at h
        simp only [truncate,centeredSum,ite_eq_right he]
        rw [ih l (by omega)]

variable [Fintype E] [DecidableEq E]

lemma centeredSum_moments (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hf : LazyDFS.Fresh w p used) :
    expect w (t.centeredSum p) = 0 ∧
      expect w (fun ω => (t.centeredSum p ω)^2) =
        p*(1-p)*expect w (fun ω => (t.queryCount ω : ℝ)) := by
  induction t generalizing used w with
  | done r => simp [centeredSum,queryCount,expect_const w hw]
  | ask e l r hl hr =>
    have h0 := hl (insert e used) ht.2.1 (pin w e False)
      (pin_normalized w hw e False) (LazyDFS.fresh_pin w p used hf e False)
    have h1 := hr (insert e used) ht.2.2 (pin w e True)
      (pin_normalized w hw e True) (LazyDFS.fresh_pin w p used hf e True)
    have he := hf e ht.1
    constructor
    · simp only [centeredSum]
      erw [expect_prop_ite]
      simp only [expect_add, expect_const _ (pin_normalized w hw e False),
        expect_const _ (pin_normalized w hw e True),h0.1,h1.1,he.1,he.2]
      ring
    · have hx : (fun ω => ((.ask e l r : SearchTree E R).centeredSum p ω)^2) =
          (fun ω => if ω e then ((1-p)+r.centeredSum p ω)^2
            else (-p+l.centeredSum p ω)^2) := by funext ω; simp only [centeredSum]; split_ifs <;> rfl
      rw [hx]
      erw [expect_prop_ite,
        expect_square_add_const _ (pin_normalized w hw e False),
        expect_square_add_const _ (pin_normalized w hw e True),h0.1,h1.1,h0.2,h1.2,he.1,he.2]
      have hc : (fun ω => ((.ask e l r : SearchTree E R).queryCount ω : ℝ)) =
          (fun ω => 1+(if ω e then (r.queryCount ω : ℝ) else (l.queryCount ω : ℝ))) := by
        funext ω; simp only [queryCount]; split_ifs <;> simp
      rw [hc,expect_add]
      erw [expect_prop_ite,expect_const w hw,he.1,he.2]
      ring

lemma truncated_second_le (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : LazyDFS.Fresh w p used) (n : ℕ) :
    expect w (fun ω => ((t.truncate n).centeredSum p ω)^2) ≤ p*(1-p)*n := by
  rw [(t.truncate n).centeredSum_moments used (t.truncate_valid n used ht) p w hw hf |>.2]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))
  calc expect w (fun ω => ((t.truncate n).queryCount ω : ℝ)) ≤ expect w (fun _ => (n:ℝ)) :=
        expect_mono hn (fun ω => Nat.cast_le.mpr (t.queryCount_truncate_le n ω))
       _ = n := expect_const w hw _

end CriticalPercolation.SearchTree
end
end
end

end OAI
