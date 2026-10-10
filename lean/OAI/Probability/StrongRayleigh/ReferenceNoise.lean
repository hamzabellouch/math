import OAI.Probability.StrongRayleigh.IIDNoiseIncrements
import OAI.Probability.StrongRayleigh.NoisePastIndependence

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem336AdditiveD139.ReferenceNoise

variable {I : Type u_1} {S : Type u_2} {N : Type u_3} [MeasurableSpace S] [MeasurableSpace N]

def history (X : S → I → ℝ) (B : ℝ≥0 → N → ℝ) (u : ℝ≥0)
    (ω : S × (I → N)) (i : I) (t : Set.Iic u) : ℝ :=
  (t.1 : ℝ) * X ω.1 i + B t.1 (ω.2 i)

def increment (B : ℝ≥0 → N → ℝ) (u h : ℝ≥0) (A : Finset I) (θ : I → ℝ)
    (ω : S × (I → N)) : ℝ :=
  ∑ i ∈ A, θ i * (B (u + h) (ω.2 i) - B u (ω.2 i))

def incrementVariance (h : ℝ≥0) (A : Finset I) (θ : I → ℝ) : ℝ≥0 :=
  ∑ i ∈ A, NNReal.mk (θ i ^ 2) (sq_nonneg _) * h

lemma measurable_history {X : S → I → ℝ} {B : ℝ≥0 → N → ℝ}
    (hX : ∀ i, Measurable fun x => X x i) (hB : ∀ t, Measurable (B t)) (u : ℝ≥0) :
    Measurable (history X B u) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro t
  exact (measurable_const.mul ((hX i).comp measurable_fst)).add
    ((hB t.1).comp ((measurable_pi_apply i).comp measurable_snd))

lemma measurable_increment {B : ℝ≥0 → N → ℝ}
    (hB : ∀ t, Measurable (B t)) (u h : ℝ≥0) (A : Finset I) (θ : I → ℝ) :
    Measurable (increment (S := S) B u h A θ) := by
  unfold increment
  exact Finset.measurable_sum A fun i _ =>
    (((hB (u + h)).comp ((measurable_pi_apply i).comp measurable_snd)).sub
      ((hB u).comp ((measurable_pi_apply i).comp measurable_snd))).const_mul (θ i)

variable {μ : Measure S} {P : Measure N}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {X : S → I → ℝ} {B : ℝ≥0 → N → ℝ}

theorem increment_indep_history
    (hB : IsPreBrownianReal B P) (hmB : ∀ t, Measurable (B t))
    (hX : ∀ i, Measurable fun x => X x i)
    (u h : ℝ≥0) (A : Finset I) (θ : I → ℝ) :
    IndepFun (increment B u h A θ) (history X B u)
      (μ.prod (Measure.infinitePi (fun _ : I => P))) := by
  have hQ : Measurable (fun ω : I → N =>
      ∑ i ∈ A, θ i * (B (u + h) (ω i) - B u (ω i))) := by
    exact Finset.measurable_sum A fun i _ =>
      (((hmB (u + h)).comp (measurable_pi_apply i)).sub
        ((hmB u).comp (measurable_pi_apply i))).const_mul (θ i)
  exact NoisePast.indepFun_snd_observation (μ := μ) hQ
    (Measurable.of_eval fun i =>
      Measurable.of_eval fun t => (hmB t.1).comp (measurable_pi_apply i))
    (Noise.brownian_iid_weighted_increment_indep_past hB hmB u h A θ)
    (fun p : S × (I → Set.Iic u → ℝ) => fun i t => (t.1 : ℝ) * X p.1 i + p.2 i t)
    (by
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro t
      exact (measurable_const.mul ((hX i).comp measurable_fst)).add
        ((measurable_pi_apply t).comp ((measurable_pi_apply i).comp measurable_snd)))

theorem increment_hasLaw
    (hB : IsPreBrownianReal B P) (hmB : ∀ t, Measurable (B t))
    (u h : ℝ≥0) (A : Finset I) (θ : I → ℝ) :
    HasLaw (increment (S := S) B u h A θ) (gaussianReal 0 (incrementVariance h A θ))
      (μ.prod (Measure.infinitePi (fun _ : I => P))) := by
  exact (Noise.brownian_iid_weighted_increment_hasLaw hB hmB u h A θ).comp
    measurePreserving_snd.hasLaw

theorem increment_condExp_test
    {E : Type u_4} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hB : IsPreBrownianReal B P) (hmB : ∀ t, Measurable (B t))
    (hX : ∀ i, Measurable fun x => X x i)
    (u h : ℝ≥0) (A : Finset I) (θ : I → ℝ) (f : ℝ → E) (hf : Measurable f) :
    (μ.prod (Measure.infinitePi (fun _ : I => P)))[
      (fun ω => f (increment B u h A θ ω)) |
      (inferInstance : MeasurableSpace (I → Set.Iic u → ℝ)).comap (history X B u)]
      =ᵐ[μ.prod (Measure.infinitePi (fun _ : I => P))]
      fun _ => ∫ x, f x ∂gaussianReal 0 (incrementVariance h A θ) := by
  have hnoise := hf.comp (measurable_increment (S := S) hmB u h A θ)
  have hobs := measurable_history hX hmB u
  have hi := (increment_indep_history (μ := μ) hB hmB hX u h A θ).comp hf measurable_id
  have hc := condExp_indep_eq hnoise.comap_le hobs.comap_le
    (comap_measurable (fun ω => f (increment (S := S) B u h A θ ω))).stronglyMeasurable hi
  have hint :
      (∫ ω, f (increment (S := S) B u h A θ ω)
        ∂μ.prod (Measure.infinitePi (fun _ : I => P))) =
      ∫ x, f x ∂gaussianReal 0 (incrementVariance h A θ) := by
    exact (increment_hasLaw (μ := μ) hB hmB u h A θ).integral_comp hf.aestronglyMeasurable
  simpa only [hint] using hc

theorem increment_condExp_eq_zero
    (hB : IsPreBrownianReal B P) (hmB : ∀ t, Measurable (B t))
    (hX : ∀ i, Measurable fun x => X x i)
    (u h : ℝ≥0) (A : Finset I) (θ : I → ℝ) :
    (μ.prod (Measure.infinitePi (fun _ : I => P)))[increment B u h A θ |
      (inferInstance : MeasurableSpace (I → Set.Iic u → ℝ)).comap (history X B u)]
      =ᵐ[μ.prod (Measure.infinitePi (fun _ : I => P))] fun _ => 0 := by
  simpa only [id_eq, integral_id_gaussianReal] using
    increment_condExp_test (μ := μ) hB hmB hX u h A θ id measurable_id

lemma coe_incrementVariance (h : ℝ≥0) (A : Finset I) (θ : I → ℝ) :
    (incrementVariance h A θ : ℝ) = (h : ℝ) * ∑ i ∈ A, θ i ^ 2 := by
  simp [incrementVariance, Finset.mul_sum, mul_comm]

theorem increment_condExp_sq
    (hB : IsPreBrownianReal B P) (hmB : ∀ t, Measurable (B t))
    (hX : ∀ i, Measurable fun x => X x i)
    (u h : ℝ≥0) (A : Finset I) (θ : I → ℝ) :
    (μ.prod (Measure.infinitePi (fun _ : I => P)))[
      (fun ω => increment B u h A θ ω ^ 2) |
      (inferInstance : MeasurableSpace (I → Set.Iic u → ℝ)).comap (history X B u)]
      =ᵐ[μ.prod (Measure.infinitePi (fun _ : I => P))]
      fun _ => (h : ℝ) * ∑ i ∈ A, θ i ^ 2 := by
  have hv : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (incrementVariance h A θ)) =
      (incrementVariance h A θ : ℝ) := by
    have hv := variance_of_integral_eq_zero
      (X := fun x : ℝ => x) (μ := gaussianReal 0 (incrementVariance h A θ))
      (by fun_prop) (by simp)
    simpa using hv.symm
  filter_upwards [increment_condExp_test (μ := μ) hB hmB hX u h A θ
    (fun x => x ^ 2) (by fun_prop)] with ω hω
  exact hω.trans (hv.trans (coe_incrementVariance h A θ))

theorem increment_condExp_characteristic
    (hB : IsPreBrownianReal B P) (hmB : ∀ t, Measurable (B t))
    (hX : ∀ i, Measurable fun x => X x i)
    (u h : ℝ≥0) (A : Finset I) (θ : I → ℝ) (t : ℝ) :
    (μ.prod (Measure.infinitePi (fun _ : I => P)))[
      (fun ω => Complex.exp ((t : ℂ) * increment B u h A θ ω * Complex.I)) |
      (inferInstance : MeasurableSpace (I → Set.Iic u → ℝ)).comap (history X B u)]
      =ᵐ[μ.prod (Measure.infinitePi (fun _ : I => P))]
      fun _ => Complex.exp (-(incrementVariance h A θ : ℂ) * (t : ℂ) ^ 2 / 2) := by
  have hc := increment_condExp_test (μ := μ) hB hmB hX u h A θ
    (fun x => Complex.exp ((t : ℂ) * x * Complex.I)) (by fun_prop)
  have hf : (∫ x : ℝ, Complex.exp ((t : ℂ) * x * Complex.I)
      ∂gaussianReal 0 (incrementVariance h A θ)) =
      Complex.exp (-(incrementVariance h A θ : ℂ) * (t : ℂ) ^ 2 / 2) := by
    rw [← charFun_apply_real, charFun_gaussianReal]
    congr 1
    push_cast
    ring
  simpa only [hf] using hc

end Problem336AdditiveD139.ReferenceNoise

end

end OAI
