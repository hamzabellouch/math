import OAI.Analysis.OperatorAlgebra.VectorLpStrongConvergence
import OAI.Analysis.OperatorAlgebra.ScalarLpSuperlevel

namespace OAI

/-! Concrete spectral interval projections on vector-valued L². -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private lemma indicator_bound (s : Set ℝ) (t : ℝ) :
    ‖s.indicator (fun _ => (1 : ℂ)) t‖ ≤ 1 := by
  by_cases ht : t ∈ s <;> simp [ht]

def vectorLpProjection (s : Set ℝ) (hs : MeasurableSet s) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  boundedVectorLp volume (s.indicator (fun _ => (1 : ℂ)))
    ((measurable_const.indicator hs).aestronglyMeasurable) 1 (indicator_bound s)

lemma vectorLpProjection_ae (s : Set ℝ) (hs : MeasurableSet s)
    (f : Lp H 2 (volume : Measure ℝ)) :
    vectorLpProjection s hs f =ᵐ[volume] s.indicator (f : ℝ → H) := by
  filter_upwards [boundedVectorLp_ae volume (s.indicator (fun _ => (1 : ℂ)))
    ((measurable_const.indicator hs).aestronglyMeasurable) 1 (indicator_bound s) f] with t ht
  change (vectorLpProjection s hs f) t = _ at ht ⊢
  rw [ht]
  by_cases h : t ∈ s <;> simp [h]

lemma vectorLpProjection_norm_le (s : Set ℝ) (hs : MeasurableSet s) :
    ‖vectorLpProjection (H := H) s hs‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [vectorLpProjection_ae s hs f] with t ht
  rw [ht]
  by_cases h : t ∈ s <;> simp [h]

lemma vectorLpProjection_mul (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    vectorLpProjection (H := H) s hs * vectorLpProjection t ht =
      vectorLpProjection (s ∩ t) (hs.inter ht) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [vectorLpProjection_ae s hs (vectorLpProjection t ht f),
    vectorLpProjection_ae t ht f, vectorLpProjection_ae (s ∩ t) (hs.inter ht) f]
    with x hx hy hz
  change (vectorLpProjection s hs (vectorLpProjection t ht f)) x = _
  rw [hx, hz]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt, hy]

variable [CompleteSpace H]

lemma vectorLpProjection_star (s : Set ℝ) (hs : MeasurableSet s) :
    star (vectorLpProjection (H := H) s hs) = vectorLpProjection s hs := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [vectorLpProjection_ae s hs f, vectorLpProjection_ae s hs g] with t hf hg
  rw [hf, hg]
  by_cases ht : t ∈ s <;> simp [ht]

lemma vectorLpProjection_isStarProjection (s : Set ℝ) (hs : MeasurableSet s) :
    IsStarProjection (vectorLpProjection (H := H) s hs) := by
  apply isStarProjection_iff'.mpr
  exact ⟨by simpa only [inter_self] using vectorLpProjection_mul (H := H) s s hs hs,
    vectorLpProjection_star s hs⟩

def vectorIntervalCutoff (r : ℝ) (n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (realUpperCutoff 0 n (r - |t|) : ℂ))
    (by apply Complex.continuous_ofReal.comp; apply (realUpperCutoff_continuous 0 n).comp;
        fun_prop) 1
    (by intro t; rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (realUpperCutoff_nonneg _ _ _)]; exact realUpperCutoff_le_one _ _ _)

lemma vectorIntervalCutoff_norm (r : ℝ) (n : ℕ) (t : ℝ) :
    ‖vectorIntervalCutoff r n t‖ ≤ 1 := by
  change ‖(realUpperCutoff 0 n (r - |t|) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (realUpperCutoff_nonneg _ _ _)]
  exact realUpperCutoff_le_one _ _ _

lemma vectorIntervalCutoff_tendsto (r t : ℝ) :
    Tendsto (fun n => vectorIntervalCutoff r n t) atTop
      (𝓝 ((Icc (-r) r).indicator (fun _ => (1 : ℂ)) t)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [realUpperCutoff_eventually 0 (r - |t|)] with n hn
  change (Icc (-r) r).indicator (fun _ => (1 : ℂ)) t =
    (realUpperCutoff 0 n (r - |t|) : ℂ)
  rw [hn]
  have he : 0 ≤ r - |t| ↔ t ∈ Icc (-r) r := by
    rw [sub_nonneg, abs_le]; rfl
  by_cases ht : t ∈ Icc (-r) r <;> simp [he, ht]

lemma vectorIntervalCutoff_strong (r : ℝ) (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => vectorLpRepresentation volume (vectorIntervalCutoff r n) f)
      atTop (𝓝 (vectorLpProjection (Icc (-r) r) measurableSet_Icc f)) := by
  exact vectorLpRepresentation_strong (vectorIntervalCutoff r)
    ((Icc (-r) r).indicator (fun _ => (1 : ℂ)))
    ((measurable_const.indicator measurableSet_Icc).aestronglyMeasurable)
    1 zero_le_one (vectorIntervalCutoff_norm r) (indicator_bound _)
    (vectorIntervalCutoff_tendsto r) f

end WeakPureInfiniteness

end

end OAI
