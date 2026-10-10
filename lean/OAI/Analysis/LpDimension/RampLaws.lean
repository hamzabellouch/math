import OAI.Analysis.LpDimension.SymmetricLaws

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset
open scoped BigOperators Topology Matrix ENNReal NNReal
universe u uE uI uV

namespace SubpolynomialLp

variable {I : Type uI} {E : Type uE} [Fintype I] [Nonempty I] [Fintype E]

def paretoVectorLaw (p : ℝ) (g : I → E → ℝ) : Measure (E → ℝ) :=
  averageLaw (fun i => (pareto p).map (fun r e => g i e*r))

lemma paretoVectorLaw_probability (p : ℝ) (hp : 0 < p) (g : I → E → ℝ) :
    IsProbabilityMeasure (paretoVectorLaw p g) := by
  let :=  pareto_probability p hp
  have : ∀ i : I, IsProbabilityMeasure ((pareto p).map (fun r e => g i e*r)) :=
    fun _ => (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  exact averageLaw_probability _

omit [Nonempty I] [Fintype E] in
lemma normalized_coefficients_bounded (p : ℝ) (hp : 0 < p) (g : I → E → ℝ)
    (hg : ∀ e, ∑ i, |g i e|^p = 1) : ∀ i e, |g i e| ≤ 1 := by
  intro i e
  have hh : |g i e|^p ≤ 1 := by
    rw [← hg e]
    exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg (g j e)) p) (Finset.mem_univ i)
  by_contra hn
  have hpow : 1 < |g i e|^p := Real.one_lt_rpow (lt_of_not_ge hn) hp
  linarith

omit [Nonempty I] in
lemma paretoVectorLaw_integrable (p : ℝ) (g : I → E → ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (e : E)
    (hi : ∀ i, Integrable (fun r => f (g i e*r)) (pareto p)) :
    Integrable (fun z => f (z e)) (paretoVectorLaw p g) := by
  apply averageLaw_integrable
  intro i
  rw [integrable_map_measure (show Measurable (fun z : E → ℝ => f (z e)) from hf.comp (measurable_pi_apply e)).aestronglyMeasurable (by fun_prop)]
  exact hi i

omit [Nonempty I] in
lemma paretoVectorLaw_moment (p : ℝ) (hp : 0 < p) (g : I → E → ℝ)
    (hg : ∀ e, ∑ i, |g i e|^p = 1) (f : ℝ → ℝ) (hf : Measurable f)
    (hn : ∀ x, f (-x)=f x) (hz : ∀ x, |x| ≤ 1 → f x=0) (e : E)
    (hi : ∀ i, Integrable (fun r => f (g i e*r)) (pareto p)) :
    (∫ z, f (z e) ∂paretoVectorLaw p g) = (∫ r, f r ∂pareto p)/(Fintype.card I : ℝ) := by
  have habs := normalized_coefficients_bounded p hp g hg
  rw [paretoVectorLaw,averageLaw_integral]
  · have he (i : I) : (∫ z, f (z e) ∂(pareto p).map (fun r e => g i e*r)) = |g i e|^p*(∫ r, f r ∂pareto p) := by
      rw [integral_map (by fun_prop) (show Measurable (fun z : E → ℝ => f (z e)) from hf.comp (measurable_pi_apply e)).aestronglyMeasurable]
      exact pareto_even_scaling p _ hp (habs i e) f hn hz
    simp_rw [he]
    rw [← Finset.sum_mul,hg e,one_mul]
  · intro i
    rw [integrable_map_measure (show Measurable (fun z : E → ℝ => f (z e)) from hf.comp (measurable_pi_apply e)).aestronglyMeasurable (by fun_prop)]
    exact hi i

omit [Nonempty I] in
lemma paretoVectorLaw_tail_integrable (p a : ℝ) (hp : 2 < p) (g : I → E → ℝ)
    (hg : ∀ e, ∑ i, |g i e|^p = 1) (e : E) :
    Integrable (fun z => (tailPart a (z e))^2) (paretoVectorLaw p g) := by
  apply paretoVectorLaw_integrable p g (fun x => (tailPart a x)^2) (by fun_prop) e
  intro i
  exact pareto_tail_sq_integrable p a (g i e) hp (normalized_coefficients_bounded p (by linarith) g hg i e)

omit [Nonempty I] in
lemma paretoVectorLaw_tail_moment (p a : ℝ) (hp : 2 < p) (ha : 1 ≤ a)
    (g : I → E → ℝ) (hg : ∀ e, ∑ i, |g i e|^p=1) (e : E) :
    (∫ z, (tailPart a (z e))^2 ∂paretoVectorLaw p g) =
      (p/(p-2)*a^(2-p))/(Fintype.card I : ℝ) := by
  have hx : ∀ x, |x| ≤ 1 → (tailPart a x)^2 = 0 := by
    intro x hx
    simp [tailPart,not_lt.mpr (hx.trans ha)]
  rw [paretoVectorLaw_moment p (by linarith) g hg _ (by fun_prop)
    (fun x => by rw [tailPart_neg,neg_sq]) hx e]
  · congr 1
    simpa only [one_mul,abs_one,Real.one_rpow] using pareto_tail_sq_moment p a 1 hp ha (by norm_num)
  · intro i
    exact pareto_tail_sq_integrable p a (g i e) hp (normalized_coefficients_bounded p (by linarith) g hg i e)

lemma paretoVectorLaw_ramp_integrable (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (g : I → E → ℝ) (ℓ : ℕ) (e : E) :
    Integrable (fun z => |dyadicRamp ℓ (z e)|^q) (paretoVectorLaw p g) := by
  let :=  paretoVectorLaw_probability p hp g
  apply Integrable.of_bound (show Measurable (fun z : E → ℝ => |dyadicRamp ℓ (z e)|^q) by fun_prop).aestronglyMeasurable
    (((2:ℝ)^(2*ℓ))^q)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_dyadicRamp_le ℓ (z e)) hq

omit [Nonempty I] in
lemma paretoVectorLaw_ramp_moment (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (g : I → E → ℝ) (hg : ∀ e, ∑ i, |g i e|^p=1) (ℓ : ℕ) (e : E) :
    (∫ z, |dyadicRamp ℓ (z e)|^q ∂paretoVectorLaw p g) =
      (∫ r, |dyadicRamp ℓ r|^q ∂pareto p)/(Fintype.card I : ℝ) := by
  apply paretoVectorLaw_moment p hp g hg (fun x => |dyadicRamp ℓ x|^q) (by fun_prop)
    (fun x => by rw [dyadicRamp_neg,abs_neg])
    (fun x hx => by rw [dyadicRamp_zero_small _ _ hx,abs_zero,Real.zero_rpow hq.ne']) e
  intro i
  let :=  pareto_probability p hp
  apply Integrable.of_bound (show Measurable (fun r : ℝ => |dyadicRamp ℓ (g i e*r)|^q) by fun_prop).aestronglyMeasurable
    (((2:ℝ)^(2*ℓ))^q)
  apply ae_of_all
  intro r
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_dyadicRamp_le ℓ _) hq.le

lemma paretoVectorLaw_range {V : Type uV} [Fintype V]
    (p : ℝ) (g : I → E → ℝ) (A : Matrix E V ℝ)
    (hg : ∀ i, ∃ x, A.mulVec x=g i) :
    ∀ᵐ z ∂paretoVectorLaw p g, ∃ x, A.mulVec x=z := by
  classical
  have hs : MeasurableSet {z : E → ℝ | ∃ x, A.mulVec x=z} :=
    (LinearMap.range (Matrix.toLin' A)).closed_of_finiteDimensional.measurableSet
  apply averageLaw_ae
  intro i
  apply (ae_map_iff (by fun_prop) hs).mpr
  apply ae_of_all
  intro r
  obtain ⟨x,hx⟩ := hg i
  refine ⟨r • x,?_⟩
  rw [Matrix.mulVec_smul,hx]
  ext e
  simp [smul_eq_mul,mul_comm]

end SubpolynomialLp

end

end OAI
