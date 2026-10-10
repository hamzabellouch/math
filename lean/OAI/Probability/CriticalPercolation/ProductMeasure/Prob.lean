import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ExpectMulReal

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def prob (w : E → Prop → ℝ) (P : Set E → Prop) : ℝ :=
  expect w (fun ω => if P ω then 1 else 0)

lemma prob_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b) (P : Set E → Prop) :
    0 ≤ prob w P := expect_nonneg hp (fun _ => by split_ifs <;> norm_num)

lemma prob_mono (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {P Q : Set E → Prop} (h : ∀ ω, P ω → Q ω) : prob w P ≤ prob w Q := by
  apply expect_mono hp
  intro ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]
  exact (hQ (h ω hP)).elim

lemma prob_split (w : E → Prop → ℝ) (P Q : Set E → Prop) :
    prob w P = prob w (fun ω => P ω ∧ Q ω) + prob w (fun ω => P ω ∧ ¬Q ω) := by
  unfold prob
  rw [← expect_add]
  congr 1
  funext ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

lemma prob_congr (w : E → Prop → ℝ) {P Q : Set E → Prop}
    (h : ∀ ω, P ω ↔ Q ω) : prob w P = prob w Q := by
  congr 1
  funext ω
  exact propext (h ω)

lemma indicator_mask (P Q : Prop) :
    (if P then (if Q then (1 : ℝ) else 0) else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma indicator_mask_mul (P Q R : Prop) :
    (if P then (if Q then (1 : ℝ) else 0)*(if R then 1 else 0) else 0) =
      if P ∧ Q ∧ R then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

lemma indicator_antitone {X : Type*} [Preorder X] {P : X → Prop}
    (h : ∀ ⦃x y⦄, x ≤ y → P y → P x) :
    Antitone (fun x => if P x then (1 : ℝ) else 0) := by
  intro x y hxy
  by_cases hx : P x <;> by_cases hy : P y <;> simp [hx, hy]
  exact (hx (h hxy hy)).elim

lemma indicator_monotone {X : Type*} [Preorder X] {P : X → Prop}
    (h : ∀ ⦃x y⦄, x ≤ y → P x → P y) :
    Monotone (fun x => if P x then (1 : ℝ) else 0) := by
  intro x y hxy
  by_cases hx : P x <;> by_cases hy : P y <;> simp [hx, hy]
  exact (hy (h hxy hx)).elim

lemma expect_mul_ge_antitone (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hp : ∀ e b, 0 ≤ w e b) (f g : (E → Prop) → ℝ)
    (hf : Antitone f) (hg : Antitone g) :
    expect w f * expect w g ≤ expect w (fun ω => f ω*g ω) := by
  have hh := expect_mul_ge_real w hw hp (fun ω => -f ω) (fun ω => -g ω) hf.neg hg.neg
  have hn (f : (E → Prop) → ℝ) : expect w (fun ω => -f ω) = -expect w f := by
    simp [expect, Finset.sum_neg_distrib]
  simpa only [hn, neg_mul_neg] using hh

lemma prob_harris_decreasing (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hp : ∀ e b, 0 ≤ w e b) (P Q : Set E → Prop)
    (hP : ∀ ⦃ω ω'⦄, ω ≤ ω' → P ω' → P ω)
    (hQ : ∀ ⦃ω ω'⦄, ω ≤ ω' → Q ω' → Q ω) :
    prob w P * prob w Q ≤ prob w (fun ω => P ω ∧ Q ω) := by
  have hh := expect_mul_ge_antitone w hw hp _ _ (indicator_antitone hP) (indicator_antitone hQ)
  change expect w _ * expect w _ ≤ _
  refine hh.trans_eq ?_
  apply congrArg (expect w)
  funext ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]

end CriticalPercolation.FiniteProduct

end
end

end OAI
