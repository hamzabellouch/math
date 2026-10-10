import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ProbOr
import OAI.Probability.CriticalPercolation.ProductMeasure.Potential

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_eval_indicator (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (e : E) (b : A) : expect w (fun ω => if ω e = b then 1 else 0) = w e b := by
  classical
  have ht (ω : E → A) : density w ω * (if ω e = b then 1 else 0) =
      ∏ j, w j (ω j) * (if j = e then if ω j = b then 1 else 0 else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [density]
  simp only [expect, ht]
  rw [← Fintype.prod_sum (fun j a => w j a * (if j = e then if a = b then 1 else 0 else 1))]
  have hs (j : E) : (∑ a, w j a * (if j = e then if a = b then 1 else 0 else 1)) =
      if j = e then w e b else 1 := by
    split_ifs with he
    · subst j; simp
    · simp [hw]
  simp only [hs]
  simp
end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_coordinate_mask (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) =
      w e b * expect w (fun ω => f (Function.update ω e b)) := by
  have hid : (fun ω => if ω e = b then f ω else 0) =
      (fun ω => (if ω e = b then (1:ℝ) else 0)*f (Function.update ω e b)) := by
    funext ω
    split_ifs with h
    · have hu : Function.update ω e b = ω := by rw [← h]; exact Function.update_eq_self _ _
      simp [hu]
    · simp
  rw [hid]
  have hI : DependsOn (fun ω : E → A => if ω e = b then (1:ℝ) else 0) ({e} : Set E) := by
    intro ω ω' heq
    dsimp only
    rw [heq e (Set.mem_singleton e)]
  have hF : DependsOn (fun ω => f (Function.update ω e b)) ({e} : Set E)ᶜ := by
    intro ω ω' heq
    change f (Function.update ω e b) = f (Function.update ω' e b)
    congr 1
    funext j
    by_cases hj : j = e
    · subst j; simp
    · simp only [Function.update_of_ne hj]
      exact heq j hj
  rw [expect_indep w hw _ hI hF]
  congr 1
  exact expect_eval_indicator w hw e b

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_pin_eq_force (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (b : Prop) (hb : w e b ≠ 0) (f : (E → Prop) → ℝ) :
    expect (pin w e b) f = expect w (fun ω => f (Function.update ω e b)) := by
  apply mul_left_cancel₀ hb
  exact (expect_mask_pin w e b f).symm.trans (expect_coordinate_mask w hw e b f)

lemma expect_pin_transport (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (a b : Prop) (ha : w e a ≠ 0) (hb : w e b ≠ 0) (f : (E → Prop) → ℝ) :
    expect (pin w e b) f = expect (pin w e a) (fun ω => f (Function.update ω e b)) := by
  rw [expect_pin_eq_force w hw e b hb,expect_pin_eq_force w hw e a ha]
  simp only [Function.update_idem]

lemma prob_congr_support (w : E → Prop → ℝ) (P Q : Set E → Prop)
    (h : ∀ ω, density w ω ≠ 0 → (P ω ↔ Q ω)) : prob w P = prob w Q := by
  apply expect_congr_support
  intro ω hω
  rw [h ω hω]

lemma prob_pin_transport (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (a b : Prop) (ha : w e a ≠ 0) (hb : w e b ≠ 0) (P : Set E → Prop) :
    prob (pin w e b) P = prob (pin w e a) (fun ω => P (Function.update ω e b)) := by
  exact expect_pin_transport w hw e a b ha hb (fun ω => if P ω then 1 else 0)

noncomputable def delta (w : E → Prop → ℝ) (F : Set E → Prop) (e : E) : ℝ :=
  prob (pin w e True) F - prob (pin w e False) F

def openPivot (F : Set E → Prop) (e : E) (ω : Set E) : Prop :=
  ω e ∧ F ω ∧ ¬F (Function.update ω e False)

omit [Fintype E] in
lemma openPivot_force_true (F : Set E → Prop) (e : E) (ω : Set E) :
    openPivot F e (Function.update ω e True) ↔
      F (Function.update ω e True) ∧ ¬F (Function.update ω e False) := by
  unfold openPivot
  erw [Function.update_self,Function.update_idem]
  simp only [true_and]

lemma delta_eq_pivotal (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    delta w F e = prob (pin w e False)
      (fun ω => F (Function.update ω e True) ∧ ¬F ω) := by
  rw [delta,prob_pin_transport w hw e False True he0 he1]
  have hh := prob_diff (pin w e False)
    (fun ω => F (Function.update ω e True)) F
  have he : prob (pin w e False) (fun ω => F (Function.update ω e True) ∧ F ω) =
      prob (pin w e False) F := by
    apply prob_congr
    intro ω
    constructor
    · exact And.right
    · intro h
      refine ⟨hF _ _ ?_ h,h⟩
      intro j hj
      change Function.update (ω : Set E) e True j
      by_cases hje : j = e
      · subst j; erw [Function.update_self]; trivial
      · erw [Function.update_of_ne hje]; exact hj
  erw [he] at hh
  exact hh.symm

end CriticalPercolation.FiniteProduct

end
end

end OAI
