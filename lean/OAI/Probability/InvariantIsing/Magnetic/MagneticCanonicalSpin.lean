import OAI.Probability.InvariantIsing.Fields.FieldSpinSampling
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldInverse
import OAI.Probability.InvariantIsing.Fields.SpinGroupCountVariance

namespace OAI

/-! The actual canonical spin law, including the ordinary Gaussian root.
Its mean is the physical bias derivative, so optimizing the bias gives
the requested group magnetizations exactly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldCanonicalSpinLaw (h : FieldStep) (b : ℝ) : Measure Bool :=
  (fieldTailSpinKernel (scalarFieldIncrements h) (scalarFieldIncrements_positive h) ∘ₖ
    fieldTransitionKernel 0 (NNReal.mk (h.height 0) (h.nonneg 0))
      (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
      (fieldScalarValue_regular _ (scalarFieldIncrements_positive h)
        measurable_logCosh logCosh_linearGrowth).1) b

instance fieldCanonicalSpinLaw_probability (h : FieldStep) (b : ℝ) :
    IsProbabilityMeasure (fieldCanonicalSpinLaw h b) := by
  unfold fieldCanonicalSpinLaw
  infer_instance

theorem fieldCanonicalSpinLaw_mean (h : FieldStep) (b : ℝ) :
    (∫ σ, spinValue σ ∂fieldCanonicalSpinLaw h b) = fieldBiasMean h b := by
  unfold fieldCanonicalSpinLaw
  rw [Kernel.integral_comp Integrable.of_finite]
  simp_rw [fieldTailSpinKernel_mean]
  exact fieldTransitionKernel_integral 0 _ _
    (fieldScalarValue_regular _ (scalarFieldIncrements_positive h)
      measurable_logCosh logCosh_linearGrowth).1
    (fieldScalarValue_regular _ (scalarFieldIncrements_positive h)
      measurable_logCosh logCosh_linearGrowth).2 _ b

theorem fieldCanonicalSpinLaw_magnetic_mean (h : FieldStep) {m : ℝ} (hm : |m| < 1) :
    (∫ σ, spinValue σ ∂fieldCanonicalSpinLaw h (magneticBias h m)) = m := by
  rw [fieldCanonicalSpinLaw_mean, fieldBiasMean_magneticBias h hm]

lemma spin_true_mean_of_spin_mean (μ : Measure Bool) [IsProbabilityMeasure μ]
    {m : ℝ} (hm : (∫ σ, spinValue σ ∂μ) = m) :
    (∫ σ, (if σ = true then (1 : ℝ) else 0) ∂μ) = (1 + m) / 2 := by
  have he (σ : Bool) : (if σ = true then (1 : ℝ) else 0) = (1 + spinValue σ) / 2 := by
    cases σ <;> norm_num [spinValue]
  simp_rw [he]
  have hu : μ.real Set.univ = 1 := by rw [measureReal_def, measure_univ]; norm_num
  rw [integral_div, integral_add (integrable_const _) Integrable.of_finite,
    integral_const, hu, one_smul, hm]

theorem spinGroupCount_mean_of_site_means {N : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin N → A) (a : A) (μ : Fin N → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] (m : ℝ)
    (hm : ∀ i, group i = a → (∫ σ, spinValue σ ∂μ i) = m) :
    (∫ σ : Spin N, (spinGroupCount group σ a : ℝ) ∂Measure.pi μ) =
      (spinGroupSize group a : ℝ) * ((1 + m) / 2) := by
  have hi (σ : Spin N) : (spinGroupCount group σ a : ℝ) =
      ∑ i, spinGroupCountSummand group a i (σ i) := (sum_spinGroupCountSummand group a σ).symm
  simp_rw [hi]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  have hj (i : Fin N) :
      (∫ σ : Spin N, spinGroupCountSummand group a i (σ i) ∂Measure.pi μ) =
        if group i = a then (1 + m) / 2 else 0 := by
    rw [integral_comp_eval (μ := μ) (i := i) (measurable_of_finite _).aestronglyMeasurable]
    by_cases hg : group i = a
    · simpa only [spinGroupCountSummand, hg, true_and, ite_true] using
        spin_true_mean_of_spin_mean (μ i) (hm i hg)
    · simp [spinGroupCountSummand, hg]
  simp_rw [hj]
  simp [Finset.sum_ite, spinGroupSize, mul_comm]

theorem magneticCanonical_projection_distance {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hcount : ∀ a, (k a : ℝ) = (spinGroupSize group a : ℝ) * ((1 + m a) / 2))
    (h : FieldStep) :
    (∫ σ : Spin N, (hammingDist σ (spinGroupProjection group k hk σ) : ℝ)
      ∂Measure.pi (fun i => fieldCanonicalSpinLaw h (magneticBias h (m (group i))))) ≤
        ∑ a, Real.sqrt (spinGroupSize group a) := by
  apply spinGroupProjection_product_mean_distance
  intro a
  rw [spinGroupCount_mean_of_site_means group a _ (m a) (fun i hi => by
    rw [hi]
    exact fieldCanonicalSpinLaw_magnetic_mean h (hm a))]
  exact (hcount a).symm

end InvariantIsing

end

end OAI
