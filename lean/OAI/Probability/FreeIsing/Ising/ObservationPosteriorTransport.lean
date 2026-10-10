import OAI.Probability.FreeIsing.Ising.ObservationLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingObservationInnovation

theorem measurePreserving_uniformObservation {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) :
    MeasurePreserving (uniformObservation (d := d))
      (μ.prod (labelMeasure d)) (observationLaw μ) :=
  ⟨measurable_uniformObservation, rfl⟩

theorem measurable_posterior {d : ℕ} (beta : ℝ) (v : TreeVertex d) (t : ℝ≥0) :
    Measurable (posterior beta v t) :=
  (((posterior_progressive beta v).stronglyAdapted t).mono
    ((filtration d).le t)).measurable

theorem posterior_memLp {d : ℕ} (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (v : TreeVertex d) (t : ℝ≥0) (p : ℝ≥0∞) :
    MemLp (posterior beta v t) p (observationLaw μ) :=
  MemLp.of_bound (measurable_posterior beta v t).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => posterior_norm_le_one beta v t x))

theorem posterior_uniformObservation {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (q : IsingInnovation.State d ℝ) :
    posterior beta v t (uniformObservation q) =
      infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (q.1 i) + WienerSampler.sample (q.2 i) t) := by
  change infiniteGibbsSpinMean beta v
    (fun i => WienerSampler.sample (q.2 i) t + (t : ℝ) * spinSign (q.1 i)) = _
  exact congrArg (infiniteGibbsSpinMean beta v) (funext (fun i => add_comm _ _))

theorem integral_posterior_pair_eq_uniform {d : ℕ} (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) (v w : TreeVertex d)
    (s t : ℝ≥0) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    (∫ x, f (posterior beta v s x, posterior beta w t x) ∂observationLaw μ) =
      ∫ q, f
        (infiniteGibbsSpinMean beta v
          (fun i => (s : ℝ) * spinSign (q.1 i) + WienerSampler.sample (q.2 i) s),
         infiniteGibbsSpinMean beta w
          (fun i => (t : ℝ) * spinSign (q.1 i) + WienerSampler.sample (q.2 i) t))
        ∂μ.prod (labelMeasure d) := by
  have hf' : AEStronglyMeasurable
      (fun x : Paths d => f (posterior beta v s x, posterior beta w t x))
      (observationLaw μ) :=
    (hf.comp ((measurable_posterior beta v s).prodMk
      (measurable_posterior beta w t))).aestronglyMeasurable
  calc
    _ = ∫ q, f (posterior beta v s (uniformObservation q),
        posterior beta w t (uniformObservation q)) ∂μ.prod (labelMeasure d) :=
      ((measurePreserving_uniformObservation μ).hasLaw.integral_comp hf').symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => congrArg f
        (Prod.ext (posterior_uniformObservation beta v s q)
          (posterior_uniformObservation beta w t q))

theorem integral_posterior_sub_sq_eq_uniform {d : ℕ} (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) (v : TreeVertex d) (s t : ℝ≥0) :
    (∫ x, (posterior beta v s x - posterior beta v t x) ^ 2 ∂observationLaw μ) =
      ∫ q, (infiniteGibbsSpinMean beta v
          (fun i => (s : ℝ) * spinSign (q.1 i) + WienerSampler.sample (q.2 i) s) -
        infiniteGibbsSpinMean beta v
          (fun i => (t : ℝ) * spinSign (q.1 i) + WienerSampler.sample (q.2 i) t)) ^ 2
        ∂μ.prod (labelMeasure d) :=
  integral_posterior_pair_eq_uniform beta μ v v s t
    ((measurable_fst.sub measurable_snd).pow_const 2)

end Problem367.IsingObservationInnovation

end

end OAI
