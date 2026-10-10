import OAI.Probability.PosteriorReplicas.Information.FiniteKL

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma sum_probability_atoms {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (q : Measure W) [IsProbabilityMeasure q] :
    ∑ w, q.real {w} = 1 := by
  simp

lemma neg_mul_log_le_tangent {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) :
    -p*Real.log p ≤ -p*Real.log r + r-p := by
  rcases hp.eq_or_lt with h | h
  · subst p
    simpa using hr.le
  · have hl := Real.one_sub_inv_le_log_of_pos (div_pos h hr)
    rw [Real.log_div h.ne' hr.ne', inv_div] at hl
    have hh := mul_le_mul_of_nonneg_left hl h.le
    rw [mul_sub, mul_div_cancel₀ _ h.ne'] at hh
    nlinarith

lemma finiteEntropy_le_log_card {W : Type*} [Fintype W] [Nonempty W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (q : Measure W) [IsProbabilityMeasure q] :
    finiteEntropy q ≤ Real.log (Fintype.card W : ℝ) := by
  have hn : 0 < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
    neg_mul_log_le_tangent (measureReal_nonneg (μ := q) (s := {w})) (inv_pos.mpr hn))
  simp only [Real.log_inv, neg_mul_neg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, sum_probability_atoms q, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_inv_cancel₀ hn.ne', one_mul, add_sub_cancel_right] at h
  exact h

lemma log_le_tangent {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ Real.log a + x/a - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div hx.ne' ha.ne'] at h
  linarith

lemma finite_weighted_log_le {W : Type*} [Fintype W] (p x : W → ℝ)
    (hp : ∀ w, 0 ≤ p w) (hpsum : ∑ w, p w = 1) (hx : ∀ w, 0 < x w) :
    ∑ w, p w * Real.log (x w) ≤ Real.log (∑ w, p w*x w) := by
  have ha : 0 < ∑ w, p w*x w := by
    have he : ∃ w, 0 < p w := by
      by_contra! hh
      have hz : ∑ w, p w = 0 := Finset.sum_eq_zero (fun w _ => le_antisymm (hh w) (hp w))
      linarith
    obtain ⟨w,hw⟩ := he
    exact Finset.sum_pos' (fun w _ => mul_nonneg (hp w) (hx w).le)
      ⟨w,Finset.mem_univ w,mul_pos hw (hx w)⟩
  have h := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
    mul_le_mul_of_nonneg_left (log_le_tangent (hx w) ha) (hp w))
  simp only [mul_sub,mul_add,← mul_div_assoc,mul_one] at h
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_div,
    hpsum,one_mul,div_self ha.ne',add_sub_cancel_right] at h
  exact h

lemma finiteEntropy_log_average {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (q : Measure W) [IsProbabilityMeasure q]
    {a : ℝ} (ha : 0 < a) :
    ∑ w, q.real {w} * Real.log (a - Real.log (q.real {w})) ≤
      Real.log (a + finiteEntropy q) := by
  have hx (w : W) : 0 < a - Real.log (q.real {w}) := by
    have hlog := Real.log_nonpos (measureReal_nonneg (μ := q) (s := {w}))
      (measureReal_le_one (μ := q) (s := {w}))
    linarith
  have h := finite_weighted_log_le (fun w => q.real {w})
    (fun w => a - Real.log (q.real {w})) (fun _ => measureReal_nonneg)
    (sum_probability_atoms q) hx
  have he : ∑ w, q.real {w}*(a-Real.log (q.real {w})) = a+finiteEntropy q := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,sum_probability_atoms q,one_mul]
    simp only [finiteEntropy,neg_mul,Finset.sum_neg_distrib,sub_eq_add_neg]
  rwa [he] at h

end PosteriorReplicas
end

end OAI
