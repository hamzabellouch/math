import Mathlib

namespace OAI

/-!
# Arctangent centers of probability laws

Every real probability law has a unique arctangent center without moment assumptions.
The center depends only on the law, is translation-equivariant, and is continuous
for weak convergence. Convergence of translated log-diameter laws yields scalar
normalization limits; no FK/spanning-tree GHP convergence theorem is asserted.
-/

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

noncomputable section
namespace MetricMeasureLimits.DiameterCenter

/-- Expected arctangent after centering at a deterministic real number. -/
def score (μ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  ∫ y, Real.arctan (y - t) ∂(μ : Measure ℝ)

private lemma norm_arctan_le (x : ℝ) : ‖Real.arctan x‖ ≤ Real.pi / 2 := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨(Real.arctan_mem_Ioo x).1.le, (Real.arctan_mem_Ioo x).2.le⟩

lemma integrable_score (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    Integrable (fun y => Real.arctan (y - t)) (μ : Measure ℝ) := by
  apply (integrable_const (Real.pi / 2)).mono'
  · exact (Real.continuous_arctan.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  · exact ae_of_all _ fun y => norm_arctan_le (y - t)

lemma continuous_score (μ : ProbabilityMeasure ℝ) : Continuous (score μ) := by
  refine continuous_of_dominated (bound := fun _ => Real.pi / 2) ?_ ?_
    (integrable_const _) ?_
  · intro t
    exact (Real.continuous_arctan.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ fun y => norm_arctan_le (y - t)
  · exact ae_of_all _ fun y =>
      Real.continuous_arctan.comp (continuous_const.sub continuous_id)

lemma strictAnti_score (μ : ProbabilityMeasure ℝ) : StrictAnti (score μ) := by
  intro s t hst
  have hpos (y : ℝ) : 0 < Real.arctan (y - s) - Real.arctan (y - t) := by
    exact sub_pos.mpr (Real.arctan_strictMono (sub_lt_sub_left hst y))
  have hint : Integrable (fun y => Real.arctan (y - s) - Real.arctan (y - t))
      (μ : Measure ℝ) := (integrable_score μ s).sub (integrable_score μ t)
  have hsupp : Function.support (fun y => Real.arctan (y - s) - Real.arctan (y - t))
      = Set.univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hpos y).ne'
  have hi : 0 < ∫ y, Real.arctan (y - s) - Real.arctan (y - t) ∂(μ : Measure ℝ) := by
    rw [integral_pos_iff_support_of_nonneg (fun y => (hpos y).le) hint, hsupp]
    simp
  rw [integral_sub (integrable_score μ s) (integrable_score μ t)] at hi
  exact sub_pos.mp hi

lemma tendsto_score_atTop (μ : ProbabilityMeasure ℝ) :
    Tendsto (score μ) atTop (𝓝 (-(Real.pi / 2))) := by
  have h : Tendsto (score μ) atTop
      (𝓝 (∫ _ : ℝ, -(Real.pi / 2) ∂(μ : Measure ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => Real.pi / 2) ?_ ?_ (integrable_const _) ?_
    · exact Eventually.of_forall fun t => (integrable_score μ t).aestronglyMeasurable
    · exact Eventually.of_forall fun t => ae_of_all _ fun y => norm_arctan_le (y - t)
    · refine ae_of_all _ fun y => ?_
      apply Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds |>.comp
      change Tendsto (fun t : ℝ => y - t) _ _
      simpa only [sub_eq_add_neg] using
        tendsto_atBot_add_const_left atTop y tendsto_neg_atTop_atBot
  simpa using h

lemma tendsto_score_atBot (μ : ProbabilityMeasure ℝ) :
    Tendsto (score μ) atBot (𝓝 (Real.pi / 2)) := by
  have h : Tendsto (score μ) atBot
      (𝓝 (∫ _ : ℝ, Real.pi / 2 ∂(μ : Measure ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => Real.pi / 2) ?_ ?_ (integrable_const _) ?_
    · exact Eventually.of_forall fun t => (integrable_score μ t).aestronglyMeasurable
    · exact Eventually.of_forall fun t => ae_of_all _ fun y => norm_arctan_le (y - t)
    · refine ae_of_all _ fun y => ?_
      apply Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp
      change Tendsto (fun t : ℝ => y - t) _ _
      simpa only [sub_eq_add_neg] using
        tendsto_atTop_add_const_left atBot y tendsto_neg_atBot_atTop
  simpa using h

/-- Every real probability law has a unique arctangent center, without a
moment assumption. This is the existence/uniqueness part of `measure:center`. -/
theorem existsUnique_center (μ : ProbabilityMeasure ℝ) :
    ∃! t : ℝ, score μ t = 0 := by
  have hneg : ∃ t, score μ t < 0 :=
    ((tendsto_score_atTop μ).eventually_lt_const (by have := Real.pi_pos; linarith)).exists
  have hpos : ∃ t, 0 < score μ t :=
    ((tendsto_score_atBot μ).eventually_const_lt (by have := Real.pi_pos; linarith)).exists
  obtain ⟨m, hm⟩ := mem_range_of_exists_le_of_exists_ge (continuous_score μ)
    (hneg.imp fun _ h => h.le) (hpos.imp fun _ h => h.le)
  refine ⟨m, hm, ?_⟩
  intro t ht
  exact (strictAnti_score μ).injective (ht.trans hm.symm)

/-- The center is a function of the unconditional probability law alone. -/
def center (μ : ProbabilityMeasure ℝ) : ℝ := (existsUnique_center μ).choose

@[simp] theorem score_center (μ : ProbabilityMeasure ℝ) : score μ (center μ) = 0 :=
  (existsUnique_center μ).choose_spec.1

lemma center_eq_of_score_eq_zero (μ : ProbabilityMeasure ℝ) {t : ℝ}
    (ht : score μ t = 0) : center μ = t :=
  (strictAnti_score μ).injective ((score_center μ).trans ht.symm)

lemma score_pos_iff (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    0 < score μ t ↔ t < center μ := by
  rw [← score_center μ, (strictAnti_score μ).lt_iff_gt]

lemma score_neg_iff (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    score μ t < 0 ↔ center μ < t := by
  rw [← score_center μ, (strictAnti_score μ).lt_iff_gt]

/-- Push a probability law forward by translation by `c`. -/
def translate (μ : ProbabilityMeasure ℝ) (c : ℝ) : ProbabilityMeasure ℝ :=
  μ.map (fun y => y + c)

lemma score_translate (μ : ProbabilityMeasure ℝ) (c t : ℝ) :
    score (translate μ c) (t + c) = score μ t := by
  unfold score translate
  rw [ProbabilityMeasure.toMeasure_map, integral_map_of_stronglyMeasurable
    (measurable_id'.add_const c)]
  · congr 1
    ext y
    congr 1
    ring
  · exact (Real.continuous_arctan.comp
      (continuous_id.sub continuous_const)).stronglyMeasurable

/-- Translation equivariance in `measure:center`. -/
theorem center_translate (μ : ProbabilityMeasure ℝ) (c : ℝ) :
    center (translate μ c) = center μ + c := by
  apply center_eq_of_score_eq_zero
  rw [score_translate, score_center]

/-- A bounded continuous arctangent test of a law. -/
def arctanTest (t : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => Real.arctan (y - t),
      Real.continuous_arctan.comp (continuous_id.sub continuous_const)⟩ Real.pi
    (fun x y => by
      calc
        dist (Real.arctan (x - t)) (Real.arctan (y - t))
            ≤ ‖Real.arctan (x - t)‖ + ‖Real.arctan (y - t)‖ := dist_le_norm_add_norm _ _
        _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add (norm_arctan_le _) (norm_arctan_le _)
        _ = Real.pi := by ring)

lemma continuous_score_law (t : ℝ) : Continuous (fun μ : ProbabilityMeasure ℝ => score μ t) :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction (arctanTest t)

/-- Continuity under weak convergence of real probability laws in
`measure:center`. The filter is arbitrary, not just a filter on subsequences. -/
theorem tendsto_center {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (h : Tendsto μs l (𝓝 μ)) :
    Tendsto (fun i => center (μs i)) l (𝓝 (center μ)) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    have ht := ((continuous_score_law a).tendsto μ).comp h
    have he := ht.eventually_const_lt ((score_pos_iff μ a).mpr ha)
    filter_upwards [he] with i hi
    exact (score_pos_iff (μs i) a).mp hi
  · intro b hb
    have ht := ((continuous_score_law b).tendsto μ).comp h
    have he := ht.eventually_lt_const ((score_neg_iff μ b).mpr hb)
    filter_upwards [he] with i hi
    exact (score_neg_iff (μs i) b).mp hi

/-- The no-moment arctangent center is continuous for the usual weak topology
on probability measures. -/
theorem continuous_center : Continuous center := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact tendsto_center tendsto_id

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Rewriting the law-level score as an expectation on a probability space.
Only measurability, not integrability of the random variable, is needed. -/
lemma score_map (P : ProbabilityMeasure Ω) (Y : Ω → ℝ)
    (hY : AEMeasurable Y (P : Measure Ω)) (t : ℝ) :
    score (P.map Y) t = ∫ ω, Real.arctan (Y ω - t) ∂(P : Measure Ω) := by
  unfold score
  rw [ProbabilityMeasure.toMeasure_map]
  exact integral_map hY (Real.continuous_arctan.comp
    (continuous_id.sub continuous_const)).aestronglyMeasurable

/-- The existence/uniqueness assertion of `measure:center` for an arbitrary
finite real random variable. The defining expectation is with respect to
its unconditional probability law. -/
theorem existsUnique_randomVariable_center (P : ProbabilityMeasure Ω) (Y : Ω → ℝ)
    (hY : AEMeasurable Y (P : Measure Ω)) :
    ∃! m : ℝ, (∫ ω, Real.arctan (Y ω - m) ∂(P : Measure Ω)) = 0 := by
  simpa only [score_map P Y hY] using existsUnique_center (P.map Y)

/-- Law equality implies equality of the centers; a change of probability
space causes no ambiguity. -/
theorem center_eq_of_law_eq {Ω' : Type*} [MeasurableSpace Ω']
    (P : ProbabilityMeasure Ω) (Y : Ω → ℝ) (_hY : AEMeasurable Y (P : Measure Ω))
    (P' : ProbabilityMeasure Ω') (Y' : Ω' → ℝ) (_hY' : AEMeasurable Y' (P' : Measure Ω'))
    (h : P.map Y = P'.map Y') : center (P.map Y) = center (P'.map Y') :=
  congrArg center h

end RandomVariables

/-!
The next lemmas establish only the scalar step in `measure:normalization`.
Here `ν` is a law of a logarithmic (truncated) diameter, and `τ` is the law
of the logarithm of the limiting diameter. No assertion that FK or tree
maps satisfy the needed distributional convergence is made.
-/

/-- The deterministic scale `exp(m(ν) - m(τ))` from the normalization lemma. -/
def diameterScale (ν τ : ProbabilityMeasure ℝ) : ℝ :=
  Real.exp (center ν - center τ)

lemma diameterScale_pos (ν τ : ProbabilityMeasure ℝ) : 0 < diameterScale ν τ :=
  Real.exp_pos _

/-- The proposed distance rescaling is positive even when no moments exist. -/
lemma inv_diameterScale_pos (ν τ : ProbabilityMeasure ℝ) : 0 < (diameterScale ν τ)⁻¹ :=
  inv_pos.mpr (diameterScale_pos ν τ)

/-- Along any already-established convergence of the centered log-diameter
laws, the deterministic scale ratio converges to the deterministic multiplier.
This is the scalar step in `measure:normalization`, not the subsequential
geometric/probabilistic input required by `thm:main`. -/
theorem tendsto_diameterScale_ratio {ι : Type*} {l : Filter ι}
    (ν : ι → ProbabilityMeasure ℝ) (τ : ProbabilityMeasure ℝ)
    (s : ι → ℝ) (hs : ∀ i, 0 < s i) (c : ℝ) (hc : 0 < c)
    (h : Tendsto (fun i => translate (ν i) (-Real.log (s i))) l
      (𝓝 (translate τ (Real.log c)))) :
    Tendsto (fun i => diameterScale (ν i) τ / s i) l (𝓝 c) := by
  have hm := (tendsto_center h).sub_const (center τ)
  simp only [center_translate] at hm
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hm
  have hterm (i : ι) :
      Real.exp (center (ν i) + -Real.log (s i) - center τ) = diameterScale (ν i) τ / s i := by
    rw [show center (ν i) + -Real.log (s i) - center τ =
      (center (ν i) - center τ) - Real.log (s i) by ring]
    rw [Real.exp_sub, Real.exp_log (hs i)]
    rfl
  simpa only [Function.comp_def, hterm, add_sub_cancel_left, Real.exp_log hc] using hexp

/-- Reciprocal scales tend to zero along such a subsequence when its
reference scale tends to infinity. This conclusion concerns only real
numbers; no GHP convergence is assumed or asserted. -/
theorem tendsto_inv_diameterScale_zero {ι : Type*} {l : Filter ι}
    (ν : ι → ProbabilityMeasure ℝ) (τ : ProbabilityMeasure ℝ)
    (s : ι → ℝ) (hs : ∀ i, 0 < s i) (c : ℝ) (hc : 0 < c)
    (h : Tendsto (fun i => translate (ν i) (-Real.log (s i))) l
      (𝓝 (translate τ (Real.log c)))) (hsInf : Tendsto s l atTop) :
    Tendsto (fun i => (diameterScale (ν i) τ)⁻¹) l (𝓝 (0 : ℝ)) := by
  have hr := (tendsto_diameterScale_ratio ν τ s hs c hc h).inv₀ hc.ne'
  have hz := tendsto_inv_atTop_zero.comp hsInf
  have hp := hr.mul hz
  have heq (i : ι) : (diameterScale (ν i) τ / s i)⁻¹ * (s i)⁻¹ =
      (diameterScale (ν i) τ)⁻¹ := by
    rw [inv_div, div_eq_mul_inv]
    field_simp [(hs i).ne', (diameterScale_pos (ν i) τ).ne']
  simpa only [Function.comp_def, heq, mul_zero] using hp

end MetricMeasureLimits.DiameterCenter

end

end OAI
