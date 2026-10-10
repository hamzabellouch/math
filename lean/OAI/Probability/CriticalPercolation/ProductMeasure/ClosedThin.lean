import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Prob

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma continuous_prob_weights (P : Set E → Prop) :
    Continuous (fun w : E → Prop → ℝ => prob w P) := by
  unfold prob expect density
  apply continuous_finsetSum
  intro ω _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro e _
  exact (continuous_apply (ω e)).comp (continuous_apply e)

noncomputable def closedThin (w : E → Prop → ℝ) (t : ℝ) (e : E) (b : Prop) : ℝ :=
  (1-t)*w e b + if b then 0 else t

omit [Fintype E] in
lemma closedThin_zero (w : E → Prop → ℝ) : closedThin w 0 = w := by
  funext e b
  simp [closedThin]

omit [Fintype E] in
lemma continuous_closedThin (w : E → Prop → ℝ) : Continuous (closedThin w) := by
  apply continuous_pi
  intro e
  apply continuous_pi
  intro b
  dsimp only [closedThin]
  split_ifs <;> fun_prop

omit [Fintype E] in
lemma closedThin_mass (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) (t : ℝ) (e : E) :
    ∑ b, closedThin w t e b = 1 := by
  have hh := hw e
  simp only [Fintype.sum_Prop] at hh ⊢
  dsimp only [closedThin]
  rw [ite_eq_left True.intro,ite_eq_right (by trivial : ¬False)]
  calc
    _ = (1-t)*(w e True+w e False)+t := by ring
    _ = 1 := by rw [hh]; ring

omit [Fintype E] in
lemma closedThin_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ∀ e b, 0 ≤ closedThin w t e b := by
  intro e b
  apply add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hp e b))
  split_ifs <;> first | exact ht.1 | exact le_rfl

omit [Fintype E] in
lemma closedThin_closed_pos (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 1) (e : E) : 0 < closedThin w t e False := by
  simp only [closedThin,ite_eq_right (by trivial : ¬False)]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) (hp e False)) ht.1

lemma prob_mul_le_of_strict (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hp : ∀ e b, 0 ≤ w e b)
    (P Q R S : Set E → Prop)
    (h : ∀ w' : E → Prop → ℝ, (∀ e, ∑ b, w' e b = 1) → (∀ e b, 0 ≤ w' e b) →
      (∀ e, 0 < w' e False) → prob w' P * prob w' Q ≤ prob w' R * prob w' S) :
    prob w P * prob w Q ≤ prob w R * prob w S := by
  have hc := continuous_closedThin w
  have hL := ((((continuous_prob_weights P).comp hc).mul
    ((continuous_prob_weights Q).comp hc)).tendsto 0).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hR := ((((continuous_prob_weights R).comp hc).mul
    ((continuous_prob_weights S).comp hc)).tendsto 0).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (n : ℕ) : (1/((n:ℝ)+1)) ∈ Set.Ioc (0:ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0:ℝ) < n+1)).mpr
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
  have hh := le_of_tendsto_of_tendsto hL hR (Filter.Eventually.of_forall (fun n : ℕ =>
    h (closedThin w (1/((n:ℝ)+1))) (closedThin_mass w hw _)
      (closedThin_nonneg w hp ⟨(hb n).1.le,(hb n).2⟩) (closedThin_closed_pos w hp (hb n))))
  simpa only [Pi.mul_apply,Function.comp_apply,closedThin_zero] using hh

end CriticalPercolation.FiniteProduct

end
end

end OAI
