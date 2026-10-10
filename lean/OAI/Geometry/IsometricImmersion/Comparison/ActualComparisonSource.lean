import OAI.Geometry.IsometricImmersion.Estimates.ActualQMomentPositive
import OAI.Geometry.IsometricImmersion.Taylor.TaylorResidual

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Taylor

def actualComparisonSource (gStar gTau : MetricField) (z : Coord → ℝ)
    (q0 : ℝ) (P : Coord → ℝ) (p : Coord) : ℝ :=
  actualShearedQForcing gStar gTau z q0 p -
    qResidual (metricInShearCoordinates gStar q0) P p

theorem actualComparisonSource_moment {gStar gTau : MetricField} {z P : Coord → ℝ}
    {q0 a delta tau : ℝ}
    (hQ : ContinuousOn (actualShearedQForcing gStar gTau z q0) (pulseStrip a delta tau))
    (hP : ContinuousOn (qResidual (metricInShearCoordinates gStar q0) P)
      (pulseStrip a delta tau)) :
    pulseWeightedMoment a delta tau (actualComparisonSource gStar gTau z q0 P) =
      pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0) -
        pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P) :=
  pulseWeightedMoment_sub hQ hP

theorem actualComparisonSource_moment_triangle {gStar gTau : MetricField} {z P : Coord → ℝ}
    {q0 a delta tau : ℝ}
    (hQ : ContinuousOn (actualShearedQForcing gStar gTau z q0) (pulseStrip a delta tau))
    (hP : ContinuousOn (qResidual (metricInShearCoordinates gStar q0) P)
      (pulseStrip a delta tau)) :
    |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| -
      |pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| ≤
        |pulseWeightedMoment a delta tau (actualComparisonSource gStar gTau z q0 P)| := by
  rw [actualComparisonSource_moment hQ hP]
  have ht : |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| ≤
      |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0) -
        pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| +
      |pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| := by
    calc
      _ = |(pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0) -
        pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)) +
          pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| := by
            congr 1
            ring
      _ ≤ _ := abs_add_le _ _
  linarith

theorem taylor_moment_absorption_threshold {R c3 : ℝ}
    (hR : 0 ≤ R) (hc3 : 0 < c3) (N : ℕ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau → ∀ delta : ℝ, 0 ≤ delta →
      R*delta/tau^(N+1) ≤ (c3/2)*delta*tau/tau^N := by
  refine ⟨max 1 (2*R/c3),le_max_left _ _,?_⟩
  intro tau ht delta hdelta
  have ht1 : 1 ≤ tau := (le_max_left _ _).trans ht
  have htpos : 0 < tau := zero_lt_one.trans_le ht1
  have hthreshold : 2*R/c3 ≤ tau := (le_max_right _ _).trans ht
  have hh := (div_le_iff₀ hc3).mp hthreshold
  have hcoeff : R/tau ≤ (c3/2)*tau := by
    calc
      R/tau ≤ R := div_le_self hR ht1
      _ ≤ (c3/2)*tau := by linarith only [hh]
  have hscale : 0 ≤ delta/tau^N := div_nonneg hdelta (pow_nonneg htpos.le N)
  calc
    _ = (R/tau)*(delta/tau^N) := by rw [pow_succ]; field_simp [htpos.ne']
    _ ≤ ((c3/2)*tau)*(delta/tau^N) := mul_le_mul_of_nonneg_right hcoeff hscale
    _ = _ := by ring

end SmoothLocal.Pulse

end

end OAI
