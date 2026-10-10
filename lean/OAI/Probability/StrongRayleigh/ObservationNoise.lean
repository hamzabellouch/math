import OAI.Probability.StrongRayleigh.Model
import OAI.Probability.StrongRayleigh.NoisePastIndependence
import OAI.Probability.StrongRayleigh.IIDNoiseIncrements

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem336AdditiveD139.ObservationNoise

variable {I : Type u_1} {Ω : Type u_2} [MeasurableSpace Ω]
  (μ : ProbabilityMeasure (I → Bool)) (P : Measure Ω) [IsProbabilityMeasure P]

def referenceMeasure : Measure ((I → Bool) × (I → Ω)) :=
  (μ : Measure (I → Bool)).prod (Measure.infinitePi (fun _ : I => P))

instance : IsProbabilityMeasure (referenceMeasure μ P) := by
  unfold referenceMeasure
  infer_instance

def history (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0)
    (ω : (I → Bool) × (I → Ω)) (i : I) (s : Set.Iic u) : ℝ :=
  (s.1 : ℝ) * boolReal (ω.1 i) + B s.1 (ω.2 i)

def increment (B : ℝ≥0 → Ω → ℝ) (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ)
    (ω : (I → Bool) × (I → Ω)) : ℝ :=
  ∑ i ∈ S, θ i * (B (u + h) (ω.2 i) - B u (ω.2 i))

def incrementVariance (h : ℝ≥0) (S : Finset I) (θ : I → ℝ) : ℝ≥0 :=
  ∑ i ∈ S, (NNReal.mk (θ i ^ 2) (sq_nonneg _)) * h

theorem incrementVariance_coe (h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    (incrementVariance h S θ : ℝ) = (h : ℝ) * ∑ i ∈ S, θ i ^ 2 := by
  simp [incrementVariance, Finset.mul_sum, mul_comm]

variable {μ P}

theorem measurable_history {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (u : ℝ≥0) :
    Measurable (history B u : ((I → Bool) × (I → Ω)) → I → Set.Iic u → ℝ) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro s
  exact (measurable_const.mul
    ((measurable_of_countable boolReal).comp ((measurable_pi_apply i).comp measurable_fst))).add
      ((hm s.1).comp ((measurable_pi_apply i).comp measurable_snd))

theorem measurable_increment {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    Measurable (increment B u h S θ : ((I → Bool) × (I → Ω)) → ℝ) := by
  unfold increment
  fun_prop

@[reducible] def historySigma (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) :
    MeasurableSpace ((I → Bool) × (I → Ω)) :=
  (inferInstance : MeasurableSpace (I → Set.Iic u → ℝ)).comap (history B u)

omit [MeasurableSpace Ω] in
theorem historySigma_mono (B : ℝ≥0 → Ω → ℝ) :
    Monotone (historySigma (I := I) B) := by
  intro u v huv
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun y : I → Set.Iic v → ℝ => fun (i : I) (s : Set.Iic u) =>
      y i ⟨s.1, le_trans s.2 huv⟩)
  · fun_prop
  · rfl

def filtration {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace ((I → Bool) × (I → Ω))) where
  seq := historySigma B
  mono' := historySigma_mono B
  le' u := (measurable_history hm u).comap_le

omit [MeasurableSpace Ω] in

theorem measurable_current_observation (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (i : I) :
    Measurable[historySigma B u]
      (fun ω : (I → Bool) × (I → Ω) =>
        (u : ℝ) * boolReal (ω.1 i) + B u (ω.2 i)) :=
  (measurable_pi_apply (⟨u, by simp⟩ : Set.Iic u)).comp
    ((measurable_pi_apply i).comp (comap_measurable (history B u)))

theorem increment_indep_history {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    IndepFun (increment B u h S θ) (history B u) (referenceMeasure μ P) := by
  have hind := Noise.brownian_iid_weighted_increment_indep_past hB hm u h S θ
  refine NoisePast.indepFun_snd_observation (μ := (μ : Measure (I → Bool)))
    (by fun_prop) (by fun_prop) hind
    (fun p : (I → Bool) × (I → Set.Iic u → ℝ) =>
      fun i s => (s.1 : ℝ) * boolReal (p.1 i) + p.2 i s) ?_
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro s
  exact (measurable_const.mul
    ((measurable_of_countable boolReal).comp ((measurable_pi_apply i).comp measurable_fst))).add
      ((measurable_pi_apply s).comp ((measurable_pi_apply i).comp measurable_snd))

theorem increment_hasLaw {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    HasLaw (increment B u h S θ) (gaussianReal 0 (incrementVariance h S θ))
      (referenceMeasure μ P) := by
  exact (Noise.brownian_iid_weighted_increment_hasLaw hB hm u h S θ).comp
    (measurePreserving_snd (μ := (μ : Measure (I → Bool)))
      (ν := Measure.infinitePi (fun _ : I => P))).hasLaw

theorem increment_condExp_gaussian {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (referenceMeasure μ P)[(fun ω => f (increment B u h S θ ω)) | historySigma B u]
      =ᵐ[referenceMeasure μ P] fun _ =>
        ∫ x, f x ∂gaussianReal 0 (incrementVariance h S θ) := by
  have hQ := measurable_increment hm u h S θ
  have hY := measurable_history (I := I) hm u
  have hind := (increment_indep_history (μ := μ) hB hm u h S θ).comp hf measurable_id
  have hc := condExp_indep_eq (hf.comp hQ).comap_le hY.comap_le
    (comap_measurable (fun ω => f (increment B u h S θ ω))).stronglyMeasurable hind
  have hi := (increment_hasLaw (μ := μ) hB hm u h S θ).integral_comp
    hf.aestronglyMeasurable
  exact hc.trans (Filter.Eventually.of_forall (fun _ => hi))

theorem increment_condExp_eq_zero {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (S : Finset I) (θ : I → ℝ) :
    (referenceMeasure μ P)[increment B u h S θ | historySigma B u]
      =ᵐ[referenceMeasure μ P] fun _ => 0 := by
  simpa only [id_eq, integral_id_gaussianReal] using
    increment_condExp_gaussian (μ := μ) hB hm u h S θ id measurable_id

end Problem336AdditiveD139.ObservationNoise

end

end OAI
