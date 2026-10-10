import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139.ReferenceObservation

variable {I : Type u_1} {W : Type u_2} [MeasurableSpace W]

abbrev Space (I : Type u_3) (W : Type u_4) := (I → Bool) × (I → W)

def law (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure W) :
    Measure (Space I W) :=
  (μ : Measure (I → Bool)).prod (Measure.infinitePi (fun _ : I => (ν : Measure W)))

instance law_isProbabilityMeasure (μ : ProbabilityMeasure (I → Bool))
    (ν : ProbabilityMeasure W) : IsProbabilityMeasure (law μ ν) := by
  unfold law
  infer_instance

variable (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure W)

theorem signal_hasLaw : HasLaw (Prod.fst : Space I W → I → Bool) μ (law μ ν) :=
  measurePreserving_fst.hasLaw

theorem noiseField_hasLaw :
    HasLaw (Prod.snd : Space I W → I → W)
      (Measure.infinitePi (fun _ : I => (ν : Measure W))) (law μ ν) :=
  measurePreserving_snd.hasLaw

theorem noise_hasLaw (i : I) :
    HasLaw (fun ω : Space I W => ω.2 i) ν (law μ ν) :=
  (measurePreserving_eval_infinitePi (fun _ : I => (ν : Measure W)) i).hasLaw.comp
    (noiseField_hasLaw μ ν)

theorem iid_noise : iIndepFun (fun i (ω : Space I W) => ω.2 i) (law μ ν) := by
  exact (iIndepFun_iff_hasLaw_Pi_infinitePi (noise_hasLaw μ ν)
    measurable_snd.aemeasurable).2 (noiseField_hasLaw μ ν)

theorem signal_indep_noiseField :
    IndepFun (Prod.fst : Space I W → I → Bool) Prod.snd (law μ ν) := by
  exact indepFun_prod measurable_id measurable_id

variable (B : ℝ≥0 → W → ℝ)

def noise (i : I) (t : ℝ≥0) (ω : Space I W) : ℝ := B t (ω.2 i)

def observation (i : I) (t : ℝ≥0) (ω : Space I W) : ℝ :=
  (t : ℝ) * boolReal (ω.1 i) + noise B i t ω

theorem noise_projection_measurePreserving (i : I) :
    MeasurePreserving (fun ω : Space I W => ω.2 i) (law μ ν) (ν : Measure W) :=
  (noise_hasLaw μ ν i).measurePreserving (by fun_prop)

theorem noise_isPreBrownian (hB : IsPreBrownianReal B (ν : Measure W)) (i : I) :
    IsPreBrownianReal (noise B i) (law μ ν) where
  hasLaw S := (hB.hasLaw S).comp (noise_hasLaw μ ν i)

theorem noise_isBrownian (hB : IsBrownianReal B (ν : Measure W)) (i : I) :
    IsBrownianReal (noise B i) (law μ ν) where
  toIsPreBrownianReal := noise_isPreBrownian μ ν B hB.toIsPreBrownianReal i
  cont := (noise_projection_measurePreserving μ ν i).quasiMeasurePreserving.ae hB.cont

theorem iid_noise_paths (hBm : ∀ t, Measurable (B t)) :
    iIndepFun (fun i (ω : Space I W) t => noise B i t ω) (law μ ν) := by
  exact (iid_noise μ ν).comp (fun _ w t => B t w) (by fun_prop)

theorem signal_indep_noise_paths (hBm : ∀ t, Measurable (B t)) :
    IndepFun (Prod.fst : Space I W → I → Bool)
      (fun (ω : Space I W) i t => noise B i t ω) (law μ ν) := by
  exact (signal_indep_noiseField μ ν).comp measurable_id
    (show Measurable (fun w : I → W => fun i t => B t (w i)) from by fun_prop)

theorem measurable_noise (hBm : ∀ t, Measurable (B t)) (i : I) (t : ℝ≥0) :
    Measurable (noise B i t) := by
  exact (hBm t).comp ((measurable_pi_apply i).comp measurable_snd)

theorem measurable_observation (hBm : ∀ t, Measurable (B t)) (i : I) (t : ℝ≥0) :
    Measurable (observation B i t) := by
  unfold observation
  have hb : Measurable boolReal := measurable_of_finite _
  exact (measurable_const.mul (hb.comp ((measurable_pi_apply i).comp measurable_fst))).add
    (measurable_noise B hBm i t)

theorem measurable_observation_joint
    (hBm : Measurable (fun p : ℝ≥0 × W => B p.1 p.2)) (i : I) :
    Measurable (fun p : ℝ≥0 × Space I W => observation B i p.1 p.2) := by
  unfold observation noise
  have hb : Measurable boolReal := measurable_of_finite _
  fun_prop

omit [MeasurableSpace W] in
theorem continuous_observation_path (hBc : ∀ w, Continuous (fun t => B t w))
    (i : I) (ω : Space I W) : Continuous (fun t => observation B i t ω) := by
  exact ((NNReal.continuous_coe).mul continuous_const).add (hBc (ω.2 i))

theorem ae_continuous_noise_paths [Countable I]
    (hB : IsBrownianReal B (ν : Measure W)) :
    ∀ᵐ ω ∂law μ ν, ∀ i : I, Continuous (fun t => noise B i t ω) :=
  ae_all_iff.2 (fun i => (noise_isBrownian μ ν B hB i).cont)

theorem ae_continuous_observation_paths [Countable I]
    (hB : IsBrownianReal B (ν : Measure W)) :
    ∀ᵐ ω ∂law μ ν, ∀ i : I, Continuous (fun t => observation B i t ω) := by
  filter_upwards [ae_continuous_noise_paths μ ν B hB] with ω hω i
  exact (NNReal.continuous_coe.mul continuous_const).add (hω i)

omit [MeasurableSpace W] in
theorem signal_real_mem_unitInterval (i : I) (ω : Space I W) :
    boolReal (ω.1 i) ∈ Set.Icc (0 : ℝ) 1 := by
  cases ω.1 i <;> simp [boolReal]

theorem integrable_signal_real (i : I) :
    Integrable (fun ω : Space I W => boolReal (ω.1 i)) (law μ ν) := by
  have hm : Measurable (fun ω : Space I W => boolReal (ω.1 i)) :=
    (measurable_of_finite boolReal).comp ((measurable_pi_apply i).comp measurable_fst)
  refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (signal_real_mem_unitInterval i ω).1]
    exact (signal_real_mem_unitInterval i ω).2

theorem integrable_observation (hB : IsPreBrownianReal B (ν : Measure W))
    (i : I) (t : ℝ≥0) : Integrable (observation B i t) (law μ ν) :=
  ((integrable_signal_real μ ν i).const_mul (t : ℝ)).add
    ((noise_isPreBrownian μ ν B hB i).integrable_eval t)

end Problem336AdditiveD139.ReferenceObservation

end

end OAI
