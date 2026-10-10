import OAI.Probability.PosteriorReplicas.Learners.KernelLearnerBridge

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal RealInnerProductSpace unitInterval
noncomputable section
namespace PosteriorRegression

namespace CompletedKernelLearner

structure Realization {d M : ℕ} (K : CompletedKernelLearner d M) where
  initial : unitInterval → Destination M
  measurable_initial : Measurable initial
  law_initial : volume.map initial = K.initial
  transition : ℕ → State M → (Vector d × ℝ) → unitInterval → Destination M
  measurable_transition : ∀ t a, @Measurable (CompletedObservation d × unitInterval)
    (Destination M) _ _ (uncurry (transition t a))
  law_transition : ∀ t a obs, volume.map (transition t a obs) = K.transition t a obs
  output : ℕ → State M → unitInterval → UnitSphere d
  measurable_output : ∀ t a, Measurable (output t a)
  law_output : ∀ t a, volume.map (output t a) = K.output t a

lemma exists_realization {d M : ℕ} (K : CompletedKernelLearner d M) : Nonempty (Realization K) := by
  have : Nonempty (UnitSphere d) := nonempty_of_isProbabilityMeasure (K.output 0 0)
  obtain ⟨i,hi,hiLaw⟩ := K.initial.exists_measurable_map_eq
  choose δ hδ hδLaw using (fun t a => (K.transition t a).exists_measurable_map_eq_unitInterval)
  choose o ho hoLaw using (fun t a => (K.output t a).exists_measurable_map_eq)
  exact ⟨⟨i,hi,hiLaw,δ,hδ,hδLaw,o,ho,hoLaw⟩⟩

def realization {d M : ℕ} (K : CompletedKernelLearner d M) : Realization K :=
  Classical.choice K.exists_realization

abbrev Coins (T : ℕ) := Fin (T+2) → unitInterval

def coinsLaw (T : ℕ) : Measure (Coins T) := Measure.pi (fun _ => volume)

instance coinsLaw_probability (T : ℕ) : IsProbabilityMeasure (coinsLaw T) := by
  unfold coinsLaw
  infer_instance

def Realization.toLearner {d M : ℕ} {K : CompletedKernelLearner d M}
    (R : Realization K) (T : ℕ) : Learner d M T (Coins T) where
  initialChoice ω := R.initial (ω 0)
  transition t ω a obs := if ht : t≤T then R.transition t a obs (ω ⟨t,by omega⟩) else (false,a)
  output t ω a := R.output t a (ω ⟨T+1,by omega⟩)

lemma Realization.transition_completed {d M T : ℕ} {K : CompletedKernelLearner d M}
    (R : Realization K) (ω : Coins T) (t : ℕ) (a : State M) :
    AEMeasurable (fun obs => ((R.toLearner T).transition t ω a obs).2) (observationReference d) := by
  by_cases ht : t≤T
  · change AEMeasurable (fun obs => (if _ : t≤T then R.transition t a obs (ω ⟨t,by omega⟩) else (false,a)).2) _
    simp only [dite_eq_left ht]
    have hm : @Measurable (CompletedObservation d) (Destination M) _ _
        (fun obs => R.transition t a obs (ω ⟨t,by omega⟩)) :=
      (R.measurable_transition t a).comp (measurable_id.prodMk measurable_const)
    apply NullMeasurable.aemeasurable
    exact measurable_snd.comp hm
  · simpa only [toLearner, dite_eq_right ht] using (aemeasurable_const :
      AEMeasurable (fun _ : Vector d × ℝ => a) (observationReference d))

lemma observation_coin_quasi {d T : ℕ} (hd : 3≤d) (i : Fin T) (j : Fin (T+2)) :
    Measure.QuasiMeasurePreserving
      (fun z : UnitSphere d × (Coins T × Samples d T) =>
        ((z.2.2 i,⟪z.2.2 i,z.1.val⟫),z.2.1 j))
      ((uniformSphere d).prod ((coinsLaw T).prod (sampleLaw d T)))
      ((observationReference d).prod (volume : Measure unitInterval)) := by
  have : NeZero d := ⟨by omega⟩
  let e : ((UnitSphere d × Samples d T) × Coins T) ≃ᵐ
      UnitSphere d × (Coins T × Samples d T) :=
    MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      MeasurableEquiv.prodComm)
  have he : MeasurePreserving e
      (((uniformSphere d).prod (sampleLaw d T)).prod (coinsLaw T))
      ((uniformSphere d).prod ((coinsLaw T).prod (sampleLaw d T))) :=
    ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := coinsLaw T))).comp
      (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) (coinsLaw T))
  have hp := MeasureTheory.QuasiMeasurePreserving.prodMap
    (sphere_sample_observation_quasi (E := Vector d) (by simpa using hd) i)
    (measurePreserving_eval (fun _ : Fin (T+2) => (volume : Measure unitInterval)) j).quasiMeasurePreserving
  have hh := hp.comp (MeasurePreserving.symm e he).quasiMeasurePreserving
  change Measure.QuasiMeasurePreserving
    (fun z : UnitSphere d × (Coins T × Samples d T) =>
      ((z.2.2 i,⟪z.1.val,z.2.2 i⟫),z.2.1 j))
    ((uniformSphere d).prod ((coinsLaw T).prod (sampleLaw d T)))
    ((observationReference d).prod (volume : Measure unitInterval)) at hh
  simpa only [real_inner_comm] using hh

lemma Realization.uniformAdmissible {d M T : ℕ} (hd : 3≤d) {K : CompletedKernelLearner d M}
    (R : Realization K) : (R.toLearner T).UniformAdmissible (coinsLaw T) := by
  refine ⟨Filter.Eventually.of_forall (fun ω t a => R.transition_completed ω t a),?_⟩
  apply Learner.uniform_experiment_of_steps
  · exact R.measurable_initial.comp (measurable_pi_apply 0)
  · intro t a i
    by_cases ht : t≤T
    · simp only [toLearner,dite_eq_left ht]
      have hm := aemeasurable_completed_prod (observationReference d) (volume : Measure unitInterval)
        (R.measurable_transition t a)
      exact hm.comp_quasiMeasurePreserving (observation_coin_quasi hd i ⟨t,by omega⟩)
    · simpa only [toLearner,dite_eq_right ht] using (aemeasurable_const : AEMeasurable
        (fun _ : UnitSphere d × (Coins T × Samples d T) => (false,a))
        ((uniformSphere d).prod ((coinsLaw T).prod (sampleLaw d T))))
  · intro t a
    exact (R.measurable_output t a).comp (measurable_pi_apply (⟨T+1,by omega⟩ : Fin (T+2)))

lemma Realization.initial_law {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K) :
    (coinsLaw T).map (R.toLearner T).initialChoice = K.initial := by
  change (coinsLaw T).map (R.initial ∘ fun ω => ω 0) = K.initial
  unfold coinsLaw
  rw [← Measure.map_map R.measurable_initial (measurable_pi_apply 0),
    (measurePreserving_eval (fun _ : Fin (T+2) => (volume : Measure unitInterval)) 0).map_eq]
  exact R.law_initial

lemma Realization.transition_law {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (t : ℕ) (ht : t≤T) (a : State M) (obs : Vector d × ℝ) :
    (coinsLaw T).map (fun ω => (R.toLearner T).transition t ω a obs) = K.transition t a obs := by
  have hm : Measurable (R.transition t a obs) :=
    (R.measurable_transition t a).comp (measurable_const.prodMk measurable_id)
  change (coinsLaw T).map (fun ω => if _ : t≤T then R.transition t a obs (ω ⟨t,by omega⟩) else (false,a)) = _
  simp only [dite_eq_left ht]
  calc
    (coinsLaw T).map (fun ω => R.transition t a obs (ω ⟨t,by omega⟩)) =
        volume.map (R.transition t a obs) := by
      change (coinsLaw T).map (R.transition t a obs ∘ (fun ω : Coins T => ω ⟨t,by omega⟩)) = _
      unfold coinsLaw
      rw [← Measure.map_map hm (measurable_pi_apply (⟨t,by omega⟩ : Fin (T+2))),
        (measurePreserving_eval (fun _ : Fin (T+2) => (volume : Measure unitInterval)) ⟨t,by omega⟩).map_eq]
    _ = _ := R.law_transition t a obs

lemma Realization.output_law {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (t : ℕ) (a : State M) :
    (coinsLaw T).map (fun ω => (R.toLearner T).output t ω a) = K.output t a := by
  change (coinsLaw T).map (R.output t a ∘ fun ω => ω ⟨T+1,by omega⟩) = _
  unfold coinsLaw
  rw [← Measure.map_map (R.measurable_output t a) (measurable_pi_apply (⟨T+1,by omega⟩ : Fin (T+2))),
    (measurePreserving_eval (fun _ : Fin (T+2) => (volume : Measure unitInterval)) ⟨T+1,by omega⟩).map_eq]
  exact R.law_output t a

end CompletedKernelLearner
end PosteriorRegression
end

end OAI
