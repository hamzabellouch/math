import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Density

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_zero (w : E → A → ℝ) : expect w (fun _ => 0) = 0 := by
  simp [expect]

lemma expect_sum {J : Type*} [Fintype J] (w : E → A → ℝ)
    (f : J → (E → A) → ℝ) :
    expect w (fun ω => ∑ j, f j ω) = ∑ j, expect w (f j) := by
  classical
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

lemma expect_nonneg {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f : (E → A) → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expect w f := by
  rw [← expect_zero w]
  exact expect_mono hw hf

noncomputable def distribution {B : Type*} [DecidableEq B]
    (w : E → A → ℝ) (φ : (E → A) → B) (b : B) : ℝ :=
  expect w (fun ω => if φ ω = b then 1 else 0)

lemma expect_comp {B : Type*} [Fintype B] [DecidableEq B]
    (w : E → A → ℝ) (φ : (E → A) → B) (f : B → ℝ) :
    expect w (fun ω => f (φ ω)) = ∑ b, distribution w φ b * f b := by
  classical
  simp only [distribution, ← expect_mul_const, ← expect_sum]
  congr 1
  funext ω
  simp

lemma distribution_nonneg {B : Type*} [DecidableEq B]
    {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    (φ : (E → A) → B) (b : B) : 0 ≤ distribution w φ b :=
  expect_nonneg hw fun _ => by split_ifs <;> norm_num

lemma distribution_mass {B : Type*} [Fintype B] [DecidableEq B]
    (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (φ : (E → A) → B) : ∑ b, distribution w φ b = 1 := by
  simpa only [mul_one] using (expect_comp w φ (fun _ => 1)).symm.trans (expect_const w hw 1)

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_const_mul (w : E → A → ℝ) (c : ℝ) (f : (E → A) → ℝ) :
    expect w (fun ω => c * f ω) = c * expect w f := by
  simp only [mul_comm c]
  exact expect_mul_const w f c
end CriticalPercolation.FiniteProduct

end
end

end OAI
