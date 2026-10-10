import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.ClosedFresh

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E]

theorem terminalProbability_eq_indicator (T : SearchTree E R) (F : Set E → Prop)
    (H : R → Prop) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hT : ∀ ω, density w ω ≠ 0 → (F ω ↔ H (T.run (fun e => decide (ω e)))))
    (ω : E → Prop) (hω : density w ω ≠ 0) :
    T.terminalProbability F w ω = if F ω then 1 else 0 := by
  induction T generalizing w with
  | done r =>
    change prob w F = _
    calc
      prob w F = prob w (fun _ => H r) := prob_congr_support w F _ hT
      _ = if H r then 1 else 0 := expect_const w hw _
      _ = if F ω then 1 else 0 := by rw [hT ω hω]; rfl
  | ask e l r hl hr =>
    have he := coordinate_ne_zero_of_density w ω hω e
    by_cases hb : ω e
    · have hb' : ω e = True := propext (iff_true_intro hb)
      have he' : w e True ≠ 0 := by simpa only [hb'] using he
      have hTr : ∀ η, density (pin w e True) η ≠ 0 →
          (F η ↔ H (r.run (fun j => decide (η j)))) := by
        intro η hη
        have hbit := density_pin_support w e True η hη
        have hh := hT η (density_pin_old_support w e True η he' hη)
        simpa only [run,hbit,decide_true,Bool.true_eq,ite_true] using hh
      change (if ω e then r.terminalProbability F (pin w e True) ω
        else l.terminalProbability F (pin w e False) ω) = _
      rw [ite_eq_left hb]
      exact hr (pin w e True) (pin_normalized w hw e True) hTr
        (density_pin_of_support w ω e True hω hb')
    · have hb' : ω e = False := propext (iff_false_intro hb)
      have he' : w e False ≠ 0 := by simpa only [hb'] using he
      have hTl : ∀ η, density (pin w e False) η ≠ 0 →
          (F η ↔ H (l.run (fun j => decide (η j)))) := by
        intro η hη
        have hbit := density_pin_support w e False η hη
        have hh := hT η (density_pin_old_support w e False η he' hη)
        simpa only [run,hbit,decide_false,Bool.false_eq_true,ite_false] using hh
      change (if ω e then r.terminalProbability F (pin w e True) ω
        else l.terminalProbability F (pin w e False) ω) = _
      rw [ite_eq_right hb]
      exact hl (pin w e False) (pin_normalized w hw e False) hTl
        (density_pin_of_support w ω e False hω hb')

variable [DecidableEq E]

theorem contact_normalization (T : SearchTree E R) (used : Finset E) (hvalid : T.Valid used)
    (p : ℝ) (C : Set E) (F : Set E → Prop) (H : R → Prop) (w v : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hv : ∀ e, ∑ b, v e b = 1)
    (hf : Fresh w p used) (hc : ClosedFresh v p C used)
    (hT : ∀ ω, density w ω ≠ 0 → (F ω ↔ H (T.run (fun e => decide (ω e)))))
    (hac : ∀ ω, density v ω ≠ 0 → density w ω ≠ 0)
    (hfail : ∀ ω, density v ω ≠ 0 → ¬F ω) :
    expect v (T.contactScore p C F w) = prob w F := by
  have ht : expect v (T.terminalProbability F w) = 0 := by
    calc
      expect v (T.terminalProbability F w) = expect v (fun _ => 0) := by
        apply expect_congr_support
        intro ω hω
        rw [terminalProbability_eq_indicator T F H w hw hT ω (hac ω hω),ite_eq_right (hfail ω hω)]
      _ = 0 := expect_zero v
  have hm := contact_mean_terminal T used hvalid p C F w v hw hv hf hc
  rw [ht,add_zero] at hm
  exact hm

end CriticalPercolation.SearchTree

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*}

noncomputable def forceClosed (w : E → Prop → ℝ) (C : Set E) (e : E) (b : Prop) : ℝ :=
  if e ∈ C then (if b then 0 else 1) else w e b

variable [Fintype E]
omit [Fintype E] in
lemma forceClosed_normalized (w : E → Prop → ℝ) (C : Set E)
    (hw : ∀ e, ∑ b, w e b = 1) : ∀ e, ∑ b, forceClosed w C e b = 1 := by
  intro e
  by_cases he : e ∈ C
  · simp [forceClosed,he,Fintype.univ_Prop]
  · simpa only [forceClosed,ite_eq_right he] using hw e

omit [Fintype E] in
lemma forceClosed_nonneg (w : E → Prop → ℝ) (C : Set E)
    (hn : ∀ e b, 0 ≤ w e b) : ∀ e b, 0 ≤ forceClosed w C e b := by
  intro e b
  unfold forceClosed
  split_ifs <;> first | positivity | exact hn e b

lemma forceClosed_support (w : E → Prop → ℝ) (C : Set E) (ω : E → Prop)
    (hω : density (forceClosed w C) ω ≠ 0) : ∀ e ∈ C, ¬ω e := by
  intro e he hopen
  have h := coordinate_ne_zero_of_density (forceClosed w C) ω hω e
  simp only [forceClosed,ite_eq_left he,ite_eq_left hopen,ne_eq,not_true_eq_false] at h

omit [Fintype E] in
lemma homogeneous_normalized (w : E → Prop → ℝ) (p : ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    ∀ e, ∑ b, w e b = 1 := by
  intro e
  simp [Fintype.univ_Prop,h0,h1]

omit [Fintype E] in
lemma homogeneous_positive (w : E → Prop → ℝ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    ∀ e b, 0 < w e b := by
  intro e b
  by_cases hb : b
  · have : b = True := propext (iff_true_intro hb)
    rw [this,h1]; exact hp.1
  · have : b = False := propext (iff_false_intro hb)
    rw [this,h0]; exact sub_pos.mpr hp.2

lemma homogeneous_support (w : E → Prop → ℝ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Prop) :
    density w ω ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  exact (homogeneous_positive w hp h0 h1 e (ω e)).ne'

end CriticalPercolation.FiniteProduct

end
end

end OAI
