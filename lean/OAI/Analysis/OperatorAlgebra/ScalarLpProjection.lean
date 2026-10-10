import OAI.Analysis.OperatorAlgebra.ScalarLpMultiplier

namespace OAI

/-! Measurable spectral projections on scalar L² as indicator
multiplication operators. -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable (μ : Measure ℝ)

private lemma indicator_one_bound (s : Set ℝ) (t : ℝ) :
    ‖s.indicator (fun _ => (1 : ℂ)) t‖ ≤ 1 := by
  by_cases ht : t ∈ s <;> simp [ht]

def scalarLpProjection (s : Set ℝ) (hs : MeasurableSet s) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  boundedScalarLp μ (s.indicator (fun _ => (1 : ℂ)))
    ((measurable_const.indicator hs).aestronglyMeasurable) 1 (indicator_one_bound s)

lemma scalarLpProjection_ae (s : Set ℝ) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    scalarLpProjection μ s hs f =ᵐ[μ] s.indicator f := by
  filter_upwards [boundedScalarLp_ae μ (s.indicator (fun _ => (1 : ℂ)))
    ((measurable_const.indicator hs).aestronglyMeasurable) 1 (indicator_one_bound s) f]
    with t ht
  change (scalarLpProjection μ s hs f) t =
    s.indicator (fun _ => (1 : ℂ)) t * f t at ht
  rw [ht]
  by_cases h : t ∈ s <;> simp [h]

lemma scalarLpProjection_norm_le (s : Set ℝ) (hs : MeasurableSet s) :
    ‖scalarLpProjection μ s hs‖ ≤ 1 :=
  boundedScalarLp_norm_le μ _ _ 1 zero_le_one _

lemma scalarLpProjection_mul (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    scalarLpProjection μ s hs * scalarLpProjection μ t ht =
      scalarLpProjection μ (s ∩ t) (hs.inter ht) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [scalarLpProjection_ae μ s hs (scalarLpProjection μ t ht f),
    scalarLpProjection_ae μ t ht f,
    scalarLpProjection_ae μ (s ∩ t) (hs.inter ht) f] with x hx hy hz
  change (scalarLpProjection μ s hs (scalarLpProjection μ t ht f)) x = _
  rw [hx, hz]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt, hy]

lemma scalarLpProjection_idempotent (s : Set ℝ) (hs : MeasurableSet s) :
    scalarLpProjection μ s hs * scalarLpProjection μ s hs = scalarLpProjection μ s hs := by
  simpa only [inter_self] using scalarLpProjection_mul μ s s hs hs

lemma scalarLpProjection_star (s : Set ℝ) (hs : MeasurableSet s) :
    star (scalarLpProjection μ s hs) = scalarLpProjection μ s hs := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  simp only [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarLpProjection_ae μ s hs f,
    scalarLpProjection_ae μ s hs g] with t hf hg
  rw [hf, hg]
  by_cases ht : t ∈ s <;> simp [ht]

lemma scalarLpProjection_isStarProjection (s : Set ℝ) (hs : MeasurableSet s) :
    IsStarProjection (scalarLpProjection μ s hs) :=
  isStarProjection_iff'.mpr
    ⟨scalarLpProjection_idempotent μ s hs, scalarLpProjection_star μ s hs⟩

end WeakPureInfiniteness

end

end OAI
