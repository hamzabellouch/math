import OAI.Probability.InvariantIsing.Core.FiniteSpinEntropy

namespace OAI

/-! The finite probability form of Cauchy--Schwarz, including zero atoms. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma finite_weighted_sum_sq_le {X : Type*} [Fintype X]
    (p f : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hpSum : ∑ x, p x = 1) :
    (∑ x, p x * f x) ^ 2 ≤ ∑ x, p x * f x ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (p x)) (fun x => Real.sqrt (p x) * f x)
  have hm (x : X) : Real.sqrt (p x) * (Real.sqrt (p x) * f x) = p x * f x := by
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hp x)]
  simp_rw [hm, mul_pow, Real.sq_sqrt (hp _)] at hc
  simpa only [hpSum, one_mul] using hc

lemma finite_weighted_sum_abs_le_sqrt {X : Type*} [Fintype X]
    (p f : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hpSum : ∑ x, p x = 1) :
    |∑ x, p x * f x| ≤ Real.sqrt (∑ x, p x * f x ^ 2) := by
  have hn : 0 ≤ ∑ x, p x * f x ^ 2 :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (sq_nonneg _))
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hn]
  exact finite_weighted_sum_sq_le p f hp hpSum

lemma finite_integral_abs_le_sqrt_sq {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) [IsProbabilityMeasure μ] (F : X → ℝ) :
    (∫ x, |F x| ∂μ) ≤ Real.sqrt (∫ x, F x ^ 2 ∂μ) := by
  let p := fun x : X => μ.real {x}
  have hp : ∀ x, 0 ≤ p x := fun x => measureReal_nonneg
  have hsum : ∑ x, p x = 1 := by
    have he := integral_fintype (μ := μ) (f := fun _ : X => (1 : ℝ)) Integrable.of_finite
    simpa [p, measureReal_def] using he.symm
  have he := finite_weighted_sum_abs_le_sqrt p (fun x => |F x|) hp hsum
  have hn : 0 ≤ ∑ x, p x * |F x| :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (abs_nonneg _))
  simpa only [integral_fintype Integrable.of_finite, smul_eq_mul, p,
    abs_of_nonneg hn, sq_abs] using he

end InvariantIsing

end

end OAI
