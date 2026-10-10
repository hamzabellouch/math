import OAI.Probability.ClassicalON.IsingReference

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

theorem real_hasSum_exp (x : ℝ) : HasSum (fun k : ℕ => x^k/(k.factorial : ℝ)) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem hasSum_integral_mul_exp {f h : X → ℝ} (hf : Continuous f) (hh : Continuous h) :
    HasSum (fun k : ℕ => (∫ x,f x*h x^k ∂μ)/(k.factorial : ℝ))
      (∫ x,f x*Real.exp (h x) ∂μ) := by
  let F : ℕ → X → ℝ := fun k x => f x*(h x^k/(k.factorial : ℝ))
  let B : ℕ → X → ℝ := fun k x => ‖f x‖*(‖h x‖^k/(k.factorial : ℝ))
  have hF : ∀ k,AEStronglyMeasurable (F k) μ := by
    intro k
    exact (compact_integrable (show Continuous (F k) from (hf.mul ((hh.pow k).div_const _)))).aestronglyMeasurable
  have hB : ∀ k,∀ᵐ x ∂μ,‖F k x‖≤B k x := by
    intro k
    filter_upwards with x
    simp only [F,B,norm_mul,norm_div,norm_pow,Real.norm_natCast]
    exact le_rfl
  have hS : ∀ᵐ x ∂μ,Summable (fun k => B k x) := by
    filter_upwards with x
    exact ((real_hasSum_exp ‖h x‖).mul_left ‖f x‖).summable
  have hI : Integrable (fun x => ∑' k,B k x) μ := by
    have he : (fun x => ∑' k : ℕ,B k x) = (fun x => ‖f x‖*Real.exp ‖h x‖) := by
      funext x; exact ((real_hasSum_exp ‖h x‖).mul_left ‖f x‖).tsum_eq
    rw [he]
    exact compact_integrable (hf.norm.mul hh.norm.rexp)
  have hL : ∀ᵐ x ∂μ,HasSum (fun k => F k x) (f x*Real.exp (h x)) := by
    filter_upwards with x
    exact (real_hasSum_exp (h x)).mul_left (f x)
  have ht := hasSum_integral_of_dominated_convergence B hF hB hS hI hL
  simpa only [F,← mul_div_assoc,integral_div] using ht

theorem integral_mul_exp_nonneg_of_moments {f h : X → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hm : ∀ k : ℕ,0≤∫ x,f x*h x^k ∂μ) : 0≤∫ x,f x*Real.exp (h x) ∂μ :=
  (hasSum_integral_mul_exp μ hf hh).nonneg (fun k => div_nonneg (hm k) (Nat.cast_nonneg _))

theorem integral_mul_sum_exp_nonneg {E : Type uE} [Fintype E]
    {f : X → ℝ} {a : E → X → ℝ} (hf : Continuous f)
    (ha : ∀ e,Continuous (a e)) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (hm : ∀ (k : ℕ) (p : Fin k → E),0≤∫ x,f x*∏ i,a (p i) x ∂μ) :
    0≤∫ x,f x*Real.exp (∑ e,b e*a e x) ∂μ := by
  apply integral_mul_exp_nonneg_of_moments μ hf (by fun_prop)
  intro k
  simp_rw [Fintype.sum_pow,Finset.mul_sum]
  rw [integral_finsetSum _ (fun p _ => compact_integrable (by fun_prop))]
  apply Finset.sum_nonneg
  intro p _
  have he : (fun x => f x*∏ i,b (p i)*a (p i) x)=
      (fun x => (∏ i,b (p i))*(f x*∏ i,a (p i) x)) := by
    funext x; rw [Finset.prod_mul_distrib]; ring
  rw [he,integral_const_mul]
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => hb (p i))) (hm k p)

end
end ClassicalON

end

end OAI
