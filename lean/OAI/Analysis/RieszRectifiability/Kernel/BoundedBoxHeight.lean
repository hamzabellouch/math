import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.LocalSupportConvergence
import OAI.Analysis.RieszRectifiability.Limits.BoundedBoxConvergence

namespace OAI

/-!
# Projection-height control on bounded boxes

Convergence to a coordinate-plane measure, together with local lower mass bounds, forces
the restricted measures into arbitrarily thin tubes about the coordinate plane. The height
estimate is stated almost everywhere for the bounded projection measures used in boxwise
kernel comparisons.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem boundedProjectionFiniteMeasure_height {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hlocal : CompactTestConvergence μ (coordinatePlaneMeasure e)) (H : ℕ)
    (hball : ∀ r : ℝ, 0 < r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, ∀ x ∈ ball (e 0) (planeBoxOuterRadius K H),
        x ∈ (μ j).support → c ≤ (μ j).real (ball x r)) :
    ∀ k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(boundedProjectionFiniteMeasure (μ j) π (e 0) K H : Measure (Ambient d)),
        dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k := by
  let : IsFiniteMeasureOnCompacts (coordinatePlaneMeasure e) :=
    coordinatePlaneMeasure_finite_on_compacts e π he.continuous.measurable Q hπ hleft
  have hzero : ∀ᵐ x ∂coordinatePlaneMeasure e, dist x (e (π x)) = 0 := by
    filter_upwards [coordinatePlaneMeasure_ae_section e π he.continuous hπ.continuous hleft]
      with x hx
    rw [hx, dist_self]
  have h := compactTestConvergence_dyadic_tubes μ (coordinatePlaneMeasure e) hlocal
    (fun x => dist x (e (π x))) (1 + K * Q) (projectionHeight_lipschitz e π K Q he hπ)
    hzero (e 0) (planeBoxOuterRadius K H) hball
  intro k
  filter_upwards [h k] with j hj
  exact ae_mono (Measure.restrict_mono_set (μ j)
    (show boundedProjectionRegion π (e 0) K H ⊆ ball (e 0) (planeBoxOuterRadius K H) from
      fun _ hx => hx.2)) hj

theorem eventual_lower_ball_mass_of_AD_lower {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, ∀ x ∈ (μ j).support, c ≤ (μ j).real (ball x r) := by
  have hc : 0 < r ^ n / C := div_pos (pow_pos hr n) hC
  refine ⟨r ^ n / C, hc, ?_⟩
  filter_upwards [hdiam r hr] with j hj
  intro x hx
  have hfinite : (μ j) (ball x r) ≠ ∞ :=
    ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top)
  have h := ENNReal.toReal_mono hfinite (hlower j x hx r ⟨hr, hj⟩)
  simpa only [ENNReal.toReal_ofReal hc.le, Measure.real] using! h

theorem boundedProjectionFiniteMeasure_height_of_AD_lower {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hlocal : CompactTestConvergence μ (coordinatePlaneMeasure e))
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ Fintype.card ι / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support) :
    ∀ H k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(boundedProjectionFiniteMeasure (μ j) π (e 0) K H : Measure (Ambient d)),
        dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k := by
  intro H
  apply boundedProjectionFiniteMeasure_height e π K Q he hπ hleft μ hlocal H
  intro r hr
  obtain ⟨c, hc, hbc⟩ := eventual_lower_ball_mass_of_AD_lower (Fintype.card ι) μ C hC hlower hdiam r hr
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbc] with j hj
  exact fun x _ hx => hj x hx

end

end RieszRectifiability

end OAI
