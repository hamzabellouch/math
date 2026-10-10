import Mathlib
import OAI.Probability.SphericalField.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma poisson_power_integral (r : ℝ≥0) (a : ℝ) :
    ∫ n, a ^ n ∂poissonMeasure r = Real.exp ((r : ℝ) * (a - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial * a^n) =
        Real.exp (-(r : ℝ)) * ∑' n : ℕ, ((r : ℝ) * a)^n / n.factorial := by
      rw [← tsum_mul_left]
      congr 1
      funext n
      rw [mul_pow]
      ring
    _ = Real.exp ((r : ℝ) * (a-1)) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*a)).tsum_eq]
      rw [← Real.exp_eq_exp_ℝ,← Real.exp_add]
      congr 1
      ring

def expNegENNReal (u : ℝ≥0∞) : ℝ := (EReal.exp (-(u : EReal))).toReal

lemma expNegENNReal_bound (u : ℝ≥0∞) : 0 ≤ expNegENNReal u ∧ expNegENNReal u ≤ 1 := by
  have hu : EReal.exp (-(u : EReal)) ≤ 1 :=
    EReal.exp_le_one_iff.mpr (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg u))
  exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hu)⟩

lemma expNegENNReal_continuous : Continuous expNegENNReal := by
  have hc : Continuous (fun u : ℝ≥0∞ => EReal.exp (-(u : EReal))) := ENNReal.continuous_exp.comp continuous_coe_ennreal_ereal.neg
  rw [continuous_iff_continuousAt]
  intro u
  apply (ENNReal.continuousAt_toReal ?_).comp hc.continuousAt
  apply ne_of_lt
  exact lt_of_le_of_lt (EReal.exp_le_one_iff.mpr
    (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg u))) ENNReal.one_lt_top

lemma expNegENNReal_finite {u : ℝ≥0∞} (hu : u ≠ ⊤) :
    expNegENNReal u = Real.exp (-u.toReal) := by
  unfold expNegENNReal
  rw [← EReal.coe_ennreal_toReal hu,← EReal.coe_neg,EReal.exp_coe,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

@[simp] lemma expNegENNReal_top : expNegENNReal ⊤ = 0 := by simp [expNegENNReal]

def poissonLaplace {S : Type*} [MeasurableSpace S] (f : S → ℝ) (η : Measure S) : ℝ :=
  expNegENNReal (∫⁻ x, ENNReal.ofReal (f x) ∂η)

lemma poissonLaplace_measurable {S : Type*} [MeasurableSpace S]
    {f : S → ℝ} (hf : Measurable f) : Measurable (poissonLaplace f) :=
  expNegENNReal_continuous.measurable.comp (Measure.measurable_lintegral hf.ennreal_ofReal)

lemma poissonLaplace_bounds {S : Type*} [MeasurableSpace S]
    (f : S → ℝ) (η : Measure S) : 0 ≤ poissonLaplace f η ∧ poissonLaplace f η ≤ 1 :=
  expNegENNReal_bound _

lemma poissonLaplace_finitePointMeasure {S : Type*} [MeasurableSpace S]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (n : ℕ) (x : Fin n → S) :
    poissonLaplace f (finitePointMeasure n x) = ∏ i : Fin n, Real.exp (-f (x i)) := by
  simp only [poissonLaplace,finitePointMeasure,lintegral_finsetSum_measure]
  simp_rw [lintegral_dirac' _ hf.ennreal_ofReal]
  rw [expNegENNReal_finite (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)),ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (hf0 _)]
  rw [← Finset.sum_neg_distrib,Real.exp_sum]

lemma finitePoissonLaw_laplace {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂finitePoissonLaw r ν =
      Real.exp ((r : ℝ) * ((∫ x, Real.exp (-f x) ∂ν) - 1)) := by
  have hi : Integrable (poissonLaplace f) (finitePoissonLaw r ν) := by
    apply Integrable.of_bound (poissonLaplace_measurable hf).aestronglyMeasurable 1
    exact ae_of_all _ fun η => by
      rw [Real.norm_eq_abs,abs_of_nonneg (poissonLaplace_bounds f η).1]
      exact (poissonLaplace_bounds f η).2
  rw [finitePoissonLaw,integral_sum_measure hi]
  simp_rw [integral_smul_measure]
  have hlocal (n : ℕ) :
      ∫ η, poissonLaplace f η ∂((Measure.pi fun _ : Fin n => ν).map (finitePointMeasure n)) =
        (∫ x, Real.exp (-f x) ∂ν)^n := by
    rw [integral_map (finitePointMeasure_measurable n).aemeasurable
      (poissonLaplace_measurable hf).aestronglyMeasurable]
    simp_rw [poissonLaplace_finitePointMeasure hf hf0]
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin n) (x : S) => Real.exp (-f x))]
    simp
  simp_rw [hlocal,smul_eq_mul,← measureReal_def,poissonMeasure_real_singleton]
  simpa only [integral_poissonMeasure,smul_eq_mul] using
    poisson_power_integral r (∫ x, Real.exp (-f x) ∂ν)

@[simp] lemma expNegENNReal_zero : expNegENNReal 0 = 1 := by simp [expNegENNReal]

lemma expNegENNReal_add (u v : ℝ≥0∞) :
    expNegENNReal (u+v) = expNegENNReal u * expNegENNReal v := by
  by_cases hu : u = ⊤
  · simp [hu]
  by_cases hv : v = ⊤
  · simp [hv]
  rw [expNegENNReal_finite (ENNReal.add_ne_top.mpr ⟨hu,hv⟩),
    expNegENNReal_finite hu,expNegENNReal_finite hv,ENNReal.toReal_add hu hv,
    neg_add,Real.exp_add]

lemma expNegENNReal_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) :
    expNegENNReal (∑ i ∈ s, a i) = ∏ i ∈ s, expNegENNReal (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,expNegENNReal_add,ih]

end SphericalPerceptron
end
end

end OAI
