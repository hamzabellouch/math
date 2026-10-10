import OAI.Probability.FreeIsing.Ising.CopyCavityBounds
import OAI.Probability.FreeIsing.Ising.CopySpectral

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem measurable_field_at (beta : ℝ) (t : ℝ≥0) (v : TreeVertex d) :
    Measurable (field beta v t) := by
  have hm : Measurable (posterior beta v t) :=
    (measurable_infiniteGibbsSpinMean beta v).comp
      (Measurable.of_eval (fun vertex => measurable_evaluation vertex t))
  unfold field Real.artanh
  exact ((measurable_const.add hm).div (measurable_const.sub hm)).sqrt.log

theorem memLp_field_at
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) : MemLp (field beta v t) 2 (observationLaw μ) := by
  have hobs := (IsingConditionalCopyBounds.hasLaw_observationLaw_eval μ t).identDistrib
    (show HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) from
      ⟨(measurable_observation t).aemeasurable, rfl⟩)
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hfield := hobs.comp (ha.comp (measurable_infiniteGibbsSpinMean beta v))
  apply hfield.memLp_iff.mpr
  apply MemLp.ae_eq _ (hμ.memLp_gaussianPosteriorField_two hbeta t v)
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hp
  exact (congrArg Real.artanh hp).symm

def cavityObservable (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d)
    (x : Paths d) : ℝ :=
  CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    (fun i => field beta i t x) v w

theorem measurable_cavityObservable (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d) :
    Measurable (cavityObservable hbeta t v w) :=
  (CavityArray.measurable_field_apply (tanh_nonneg_of_beta_nonneg hbeta)
    (Real.tanh_lt_one beta) v w).comp
    (Measurable.of_eval (fun vertex => measurable_field_at beta t vertex))

theorem memLp_cavityObservable
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    MemLp (cavityObservable hbeta t v w) 2 (observationLaw μ) := by
  have hd : MemLp (fun x => cavityObservable hbeta t v w x - field beta v t x) 2
      (observationLaw μ) :=
    MemLp.of_bound
      ((measurable_cavityObservable hbeta t v w).sub (measurable_field_at beta t v)).aestronglyMeasurable
      (Real.artanh (Real.tanh beta)) (Filter.Eventually.of_forall (fun x => by
        exact CavityArray.field_site_bound (tanh_nonneg_of_beta_nonneg hbeta)
          (Real.tanh_lt_one beta) (fun i => field beta i t x) v w))
  have hs := hd.add (memLp_field_at hμ hbeta t v)
  change MemLp (fun x => (cavityObservable hbeta t v w x - field beta v t x) +
    field beta v t x) 2 (observationLaw μ) at hs
  simpa only [sub_add_cancel] using hs

omit [IsProbabilityMeasure μ] in
theorem cavityObservable_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun x => cavityObservable hbeta t v w (relabel g x)) =ᵐ[observationLaw μ]
      cavityObservable hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  filter_upwards [field_array_relabel_ae hμ g t] with x hx
  unfold cavityObservable
  rw [hx]
  rfl

def cavityLogObservable (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d)
    (x : Paths d) : ℝ :=
  Real.log (responseAttenuation (Real.tanh beta) (cavityObservable hbeta t v w x))

theorem memLp_cavityLogObservable
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    MemLp (cavityLogObservable hbeta t v w) 2 (observationLaw μ) := by
  apply memLp_log_responseAttenuation _ (memLp_cavityObservable hμ hbeta t v w)
  have h0 := tanh_nonneg_of_beta_nonneg hbeta
  have h1 := Real.tanh_lt_one beta
  nlinarith

def observableDifference {f : Paths d → ℝ} (hf : MemLp f 2 (observationLaw μ)) :
    differenceSpace beta μ :=
  CopyDifference.toRangeClosure (CopyDifference.operator
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2) (hf.toLp f)

theorem observableDifference_ae {f : Paths d → ℝ} (hf : MemLp f 2 (observationLaw μ)) :
    (observableDifference (beta := beta) hf : Lp ℝ 2 (copies beta μ)) =ᵐ[copies beta μ]
      (fun q => f q.2.1 - f q.2.2) := by
  obtain ⟨hp, hq⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have h := CopyDifference.operator_ae hp hq (hf.toLp f)
  filter_upwards [h, hp.quasiMeasurePreserving.ae hf.coeFn_toLp,
    hq.quasiMeasurePreserving.ae hf.coeFn_toLp] with q hq' hl hr
  exact hq'.trans (congrArg₂ (fun a b : ℝ => a - b) hl hr)

theorem norm_observableDifference_sq {f : Paths d → ℝ} (hf : MemLp f 2 (observationLaw μ)) :
    ‖observableDifference (beta := beta) hf‖ ^ 2 =
      ∫ q, (f q.2.1 - f q.2.2) ^ 2 ∂copies beta μ := by
  change ‖(observableDifference (beta := beta) hf : Lp ℝ 2 (copies beta μ))‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [observableDifference_ae (beta := beta) hf] with q hq
  simp [hq, pow_two]

theorem norm_cavityLogDifference_sq_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (o v w : TreeVertex d) :
    ‖observableDifference (beta := beta) (memLp_cavityLogObservable hμ hbeta t v w)‖ ^ 2 ≤
      cavityLogVarianceCoefficient (Real.tanh beta) *
        ∫ q, (IsingConditionalCopyBounds.fieldDifference beta o t q) ^ 2 ∂copies beta μ := by
  rw [norm_observableDifference_sq]
  have h := integral_sitePair_log_cavity_sub_sq_le hμ hbeta t o v w
  have hm (a b : TreeVertex d) : Measurable (fun p : CavityArray.SitePair d =>
      (Real.log (responseAttenuation (Real.tanh beta)
        (CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta) p.1 a b)) -
       Real.log (responseAttenuation (Real.tanh beta)
        (CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta) p.2 a b))) ^ 2) := by
    have ht : (Real.tanh beta) ^ 2 ≤ 1 := by
      have h0 := tanh_nonneg_of_beta_nonneg hbeta
      have h1 := Real.tanh_lt_one beta
      nlinarith
    have hl := (lipschitzWith_log_responseAttenuation ht).continuous.measurable
    have hc := CavityArray.measurable_field_apply (tanh_nonneg_of_beta_nonneg hbeta)
      (Real.tanh_lt_one beta) a b
    exact ((hl.comp (hc.comp measurable_fst)).sub (hl.comp (hc.comp measurable_snd))).pow_const 2
  have hs : Measurable (fun p : CavityArray.SitePair d => (p.1 o - p.2 o) ^ 2) :=
    (((measurable_pi_apply o).comp measurable_fst).sub
      ((measurable_pi_apply o).comp measurable_snd)).pow_const 2
  dsimp only at h
  rw [integral_map (measurable_sitePair beta t).aemeasurable (hm v w).aestronglyMeasurable,
    integral_map (measurable_sitePair beta t).aemeasurable hs.aestronglyMeasurable] at h
  exact h

end Problem367.IsingCopySpectral

end

end OAI
