import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Score
import OAI.Probability.CriticalPercolation.ProductMeasure.Variance

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

lemma score_mean_step (e : E) (l r : SearchTree E R) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (h0 : w e False = 1-p) (h1 : w e True = p)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    expect w ((.ask e l r : SearchTree E R).score p F w) =
      p*(1-p)*(delta w F e)^2 + (1-p)*expect (pin w e False) (l.score p F (pin w e False)) +
      p*expect (pin w e True) (r.score p F (pin w e True)) := by
  have heq : (.ask e l r : SearchTree E R).score p F w =
      fun ω => (1-p)*delta w F e*(if openPivot F e ω then (1:ℝ) else 0) +
        if ω e then r.score p F (pin w e True) ω else l.score p F (pin w e False) ω := by
    funext ω
    by_cases h : openPivot F e ω <;> simp [score,h]
  rw [heq]
  erw [expect_add,expect_const_mul,expect_prop_ite,h0,h1]
  change (1-p)*delta w F e * prob w (openPivot F e) + _ = _
  rw [prob_openPivot w hw e (by rw [h0]; exact (sub_pos.mpr hp.2).ne')
    (by rw [h1]; exact hp.1.ne') F hF,h1]
  ring

variable [DecidableEq E]

theorem score_mean_le_variance (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : LazyDFS.Fresh w p used) (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    expect w (T.score p F w) ≤ variance w F := by
  induction T generalizing used w with
  | done r => exact (expect_const w hw 0).le.trans (variance_nonneg w hw hn F)
  | ask e l r hl hr =>
    have he := hf e hT.1
    have hlb := hl (insert e used) hT.2.1 (pin w e False) (pin_normalized w hw e False)
      (pin_nonneg w hn e False) (LazyDFS.fresh_pin w p used hf e False)
    have hrb := hr (insert e used) hT.2.2 (pin w e True) (pin_normalized w hw e True)
      (pin_nonneg w hn e True) (LazyDFS.fresh_pin w p used hf e True)
    rw [score_mean_step e l r hp w hw he.1 he.2 F hF,
      variance_split w hw hn F e hp he.1 he.2]
    have hlb' := mul_le_mul_of_nonneg_left hlb (sub_pos.mpr hp.2).le
    have hrb' := mul_le_mul_of_nonneg_left hrb hp.1.le
    linarith

end CriticalPercolation.SearchTree

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

lemma pivotal_contribution_mean (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (h0 : w e False = 1-p) (h1 : w e True = p)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    expect w (fun ω => if openPivot F e ω then (1-p)*delta w F e else 0) =
      p*(1-p)*(delta w F e)^2 := by
  have heq : (fun ω => if openPivot F e ω then (1-p)*delta w F e else 0) =
      (fun ω => (1-p)*delta w F e*(if openPivot F e ω then (1:ℝ) else 0)) := by
    funext ω
    split_ifs <;> simp
  erw [heq,expect_const_mul]
  change (1-p)*delta w F e*prob w (openPivot F e) = _
  rw [prob_openPivot w hw e (by rw [h0]; exact (sub_pos.mpr hp.2).ne')
    (by rw [h1]; exact hp.1.ne') F hF,h1]
  ring

lemma score_second_step (e : E) (l r : SearchTree E R) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (h0 : w e False = 1-p) (h1 : w e True = p)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t)
    (hpair : expect (pin w e True) (fun ω => if openPivot F e ω then
      r.score p F (pin w e True) ω else 0) ≤ delta w F e) :
    expect w (fun ω => ((.ask e l r : SearchTree E R).score p F w ω)^2) ≤
      3*(p*(1-p)*(delta w F e)^2) +
      (1-p)*expect (pin w e False) (fun ω => (l.score p F (pin w e False) ω)^2) +
      p*expect (pin w e True) (fun ω => (r.score p F (pin w e True) ω)^2) := by
  have hd := delta_unit w hw hn e (by rw [h0]; exact (sub_pos.mpr hp.2).ne')
    (by rw [h1]; exact hp.1.ne') F hF
  have hc0 : 0 ≤ (1-p)*delta w F e := mul_nonneg (sub_pos.mpr hp.2).le hd.1
  have hc1 : (1-p)*delta w F e ≤ 1 :=
    (mul_le_mul_of_nonneg_left hd.2 (sub_pos.mpr hp.2).le).trans (by linarith [hp.1])
  have hc2 : ((1-p)*delta w F e)^2 ≤ (1-p)*delta w F e := by nlinarith
  have hbound := expect_mono hn (fun ω => show
      ((.ask e l r : SearchTree E R).score p F w ω)^2 ≤
      (if openPivot F e ω then (1-p)*delta w F e else 0) +
      (if ω e then (r.score p F (pin w e True) ω)^2 else (l.score p F (pin w e False) ω)^2) +
      2*((1-p)*delta w F e) *
        (if ω e then (if openPivot F e ω then r.score p F (pin w e True) ω else 0) else 0) from by
    by_cases hP : openPivot F e ω
    · have he := hP.1
      simp only [score,hP,he,↓reduceIte]
      nlinarith
    · by_cases he : ω e <;> simp [score,hP,he])
  erw [expect_add,expect_add,pivotal_contribution_mean w hw e hp h0 h1 F hF,
    expect_prop_ite,expect_const_mul,expect_prop_ite,h0,h1,
    expect_const _ (pin_normalized w hw e False) 0,mul_zero,add_zero] at hbound
  have hmult := mul_le_mul_of_nonneg_left hpair (mul_nonneg (by positivity : 0 ≤ 2*((1-p)*delta w F e)) hp.1.le)
  nlinarith [hbound,hmult]

end CriticalPercolation.SearchTree

end
end

end OAI
