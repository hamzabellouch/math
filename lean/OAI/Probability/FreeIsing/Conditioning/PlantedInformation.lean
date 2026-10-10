import OAI.Probability.FreeIsing.Posterior.ObservationMoments
import OAI.Probability.FreeIsing.Posterior.PlantedSymmetry

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem367.PlantedInformation

open PlantedSymmetry

variable {ι κ : Type*}

@[reducible] def observationSigma (v : ι → κ) (t : ℝ) :
    MeasurableSpace ((κ → IsingSpin) × (κ → ℝ)) :=
  MeasurableSpace.comap (fun p i => observation t p (v i)) inferInstance

theorem measurable_spinSign : Measurable spinSign := by
  intro s hs
  trivial

theorem spinSign_memLp (mu : Measure (κ → IsingSpin)) [IsFiniteMeasure mu]
    (r : κ) : MemLp (fun σ => spinSign (σ r)) 2 mu := by
  apply MemLp.of_bound (measurable_spinSign.comp (measurable_pi_apply r)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun σ => by cases h : σ r <;> norm_num [spinSign, h])

theorem observationSigma_le (v : ι → κ) (t : ℝ) :
    observationSigma v t ≤ (inferInstance : MeasurableSpace ((κ → IsingSpin) × (κ → ℝ))) := by
  apply Measurable.comap_le
  exact Measurable.of_eval (fun index =>
    (measurable_pi_apply (v index)).comp (measurable_observation t))

theorem observation_stronglyMeasurable (v : ι → κ) (t : ℝ) (i : ι) :
    StronglyMeasurable[observationSigma v t] (fun p => observation t p (v i)) :=
  ((measurable_pi_apply i).comp (comap_measurable (fun p i => observation t p (v i)))).stronglyMeasurable

theorem noise_hasLaw (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (i : κ) :
    HasLaw (fun p : (κ → IsingSpin) × (κ → ℝ) => p.2 i) (gaussianReal 0 t)
      (mu.prod (gaussianNoiseLaw κ t)) :=
  ((measurePreserving_eval_infinitePi (fun _ : κ => gaussianReal 0 t) i).comp
    measurePreserving_snd).hasLaw

theorem noise_iIndepFun (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (t : ℝ≥0) :
    iIndepFun (fun i (p : (κ → IsingSpin) × (κ → ℝ)) => p.2 i)
      (mu.prod (gaussianNoiseLaw κ t)) := by
  apply (iIndepFun_iff_hasLaw_Pi_infinitePi (noise_hasLaw mu t)
    measurable_snd.aemeasurable).mpr
  exact measurePreserving_snd.hasLaw

theorem spin_noise_indep (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (i j : κ) :
    IndepFun (fun p : (κ → IsingSpin) × (κ → ℝ) => spinSign (p.1 i))
      (fun p => p.2 j) (mu.prod (gaussianNoiseLaw κ t)) :=
  indepFun_prod (μ := mu) (ν := gaussianNoiseLaw κ t)
    (X := fun σ => spinSign (σ i)) (Y := fun B => B j)
    (measurable_spinSign.comp (measurable_pi_apply i)) (measurable_pi_apply j)

theorem integral_spin_mul_spin (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (i j : κ) :
    (∫ p, spinSign (p.1 i) * spinSign (p.1 j) ∂mu.prod (gaussianNoiseLaw κ t)) =
      ∫ σ, spinSign (σ i) * spinSign (σ j) ∂mu := by
  have hfst : HasLaw (Prod.fst : (κ → IsingSpin) × (κ → ℝ) → (κ → IsingSpin)) mu
      (mu.prod (gaussianNoiseLaw κ t)) := measurePreserving_fst.hasLaw
  exact hfst.integral_comp (f := fun σ => spinSign (σ i) * spinSign (σ j))
    (((measurable_spinSign.comp (measurable_pi_apply i)).mul
      (measurable_spinSign.comp (measurable_pi_apply j))).aestronglyMeasurable)

theorem critical_information_of_spin_sums [DecidableEq ι]
    (mu : Measure (κ → IsingSpin)) [IsProbabilityMeasure mu]
    (v : ι → κ) (hv : Function.Injective v) (r : κ)
    {t : ℝ≥0} (ht : 0 < t) (s : ℕ → Finset ι) (w : ℕ → ι → ℝ)
    (hnorm : ∀ n, ∑ i ∈ s n, w n i ^ 2 = (n : ℝ) + 1)
    (hcorrelation : ∀ n, (∑ i ∈ s n,
      w n i * ∫ σ, spinSign (σ r) * spinSign (σ (v i)) ∂mu) = (n : ℝ) + 1)
    (henergy : ∀ n, (∑ i ∈ s n, ∑ j ∈ s n,
      w n i * w n j * ∫ σ, spinSign (σ (v i)) * spinSign (σ (v j)) ∂mu) ≤
        ((n : ℝ) + 1) ^ 3) :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤
      ∫ p, (condExp (observationSigma v t) (mu.prod (gaussianNoiseLaw κ t))
        (fun q => spinSign (q.1 r)) p) ^ 2
          ∂mu.prod (gaussianNoiseLaw κ t) := by
  let P := mu.prod (gaussianNoiseLaw κ t)
  have hspin (i : κ) : MemLp (fun p : (κ → IsingSpin) × (κ → ℝ) => spinSign (p.1 i)) 2 P :=
    (spinSign_memLp mu i).comp_measurePreserving measurePreserving_fst
  apply critical_information_from_spin_sums (observationSigma_le v t)
    (fun i p => spinSign (p.1 (v i))) (fun i p => p.2 (v i)) (hspin r)
    (fun i => hspin (v i)) ht (fun i => noise_hasLaw mu t (v i))
    (fun i j hij => (noise_iIndepFun mu t).indepFun (fun heq => hij (hv heq)))
    (fun i j => spin_noise_indep mu t (v i) (v j))
    (fun i => spin_noise_indep mu t r (v i))
    (fun i => observation_stronglyMeasurable v t i) s w hnorm
  · intro n
    simpa only [P, integral_spin_mul_spin] using hcorrelation n
  · intro n
    simpa only [P, integral_spin_mul_spin] using henergy n

end Problem367.PlantedInformation

end

end OAI
