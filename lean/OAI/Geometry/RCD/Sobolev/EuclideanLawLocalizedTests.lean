import OAI.Geometry.RCD.Sobolev.WeakLocalizedTests
import OAI.Geometry.RCD.Sobolev.InnerBallCutoffSequence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

/-! # Interior ball testing of the actual measured approximation laws -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem euclideanBallProbability_null_of_volume_null {n : ℕ} {S : ℝ}
    (hS : 0<S) {s : Set (Euclidean n)} (hs : MeasurableSet s)
    (hz : (volume : Measure (Euclidean n)) s=0) :
    (euclideanBallProbability n S : Measure (Euclidean n)) s=0 := by
  have hrz : (volume.restrict (ball (0:Euclidean n) S)) s=0 := by
    rw [Measure.restrict_apply hs]
    exact measure_mono_null inter_subset_left hz
  have hzreal : (volume.restrict (ball (0:Euclidean n) S)).real s=0 := by
    rw [Measure.real,hrz,ENNReal.toReal_zero]
  have h := euclideanBallProbability_integral hS (s.indicator (fun _ => (1:ℝ)))
  rw [integral_indicator hs,integral_indicator hs,setIntegral_const,setIntegral_const] at h
  simp only [smul_eq_mul,mul_one,hzreal,mul_zero] at h
  exact (measureReal_eq_zero_iff).mp h

theorem euclideanBallProbability_null_frontier {n : ℕ} {S ρ : ℝ}
    (hS : 0<S) (hρ : 0<ρ) :
    (euclideanBallProbability n S : Measure (Euclidean n)) (frontier (ball 0 ρ))=0 :=
  euclideanBallProbability_null_of_volume_null hS isClosed_frontier.measurableSet
    (measure_mono_null frontier_ball_subset_sphere
      (Measure.addHaar_sphere_of_ne_zero volume 0 hρ.ne'))

theorem euclidean_law_ball_test_tendsto {n : ℕ} {S ρ : ℝ}
    (hS : 0<S) (hρ : 0<ρ) {ν : ℕ → ProbabilityMeasure (Euclidean n)}
    (hν : Tendsto ν atTop (𝓝 (euclideanBallProbability n S)))
    (φ : Euclidean n →ᵇ ℝ) :
    Tendsto (fun k => ∫ z in ball 0 ρ, φ z ∂(ν k : Measure (Euclidean n))) atTop
      (𝓝 (∫ z in ball 0 ρ, φ z ∂(euclideanBallProbability n S : Measure (Euclidean n)))) := by
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hν
    (euclideanBallProbability_null_frontier hS hρ)
  have hmr := (ENNReal.tendsto_toReal (measure_ne_top
    (euclideanBallProbability n S : Measure (Euclidean n)) (ball 0 ρ))).comp hm
  obtain ⟨χ,hχ,hχ0,hχlim⟩ := inner_ball_cutoff_sequence (0:Euclidean n) hρ
  exact weak_localized_test_tendsto hν measurableSet_ball hmr χ hχ hχ0 hχlim φ

end RegularPointCoordinates

end

end OAI
