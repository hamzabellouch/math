import OAI.Geometry.RCD.Coordinates.EuclideanWeakHarmonicRegularity
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace OAI

/-! # Continuous densities are determined by nonnegative compact tests -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem continuous_nonpos_of_nonnegative_tests {n : ℕ} {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) {f : Euclidean n → ℝ} (hf : ContinuousOn f Ω)
    (ht : ∀ φ : Euclidean n →ᵇ ℝ, (∀ y, 0 ≤ φ y) →
      HasCompactSupport (φ : Euclidean n → ℝ) → tsupport φ ⊆ Ω →
      (∫ y, φ y*f y) = 0) : ∀ x ∈ Ω, f x ≤ 0 := by
  intro x hx
  by_contra hle
  have hp : 0 < f x := lt_of_not_ge hle
  have hn : ∀ᶠ y in 𝓝 x, y ∈ Ω ∧ 0 < f y :=
    Filter.Eventually.and (hΩ.mem_nhds hx) ((hf.continuousAt (hΩ.mem_nhds hx)).eventually
      (eventually_gt_nhds hp))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  let χ : ContDiffBump x := ⟨δ/4,δ/2,by positivity,by linarith⟩
  have hs : tsupport (χ : Euclidean n → ℝ) ⊆ ball x δ := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by dsimp only [χ]; linarith)
  have hsΩ : tsupport (χ : Euclidean n → ℝ) ⊆ Ω :=
    fun y hy => (hball (hs hy)).1
  let φ : Euclidean n →ᵇ ℝ := ofCompactSupport χ χ.continuous χ.hasCompactSupport
  have hc : Continuous (fun y => χ y*f y) :=
    continuous_mul_of_tsupport_subset hΩ hf χ.continuous hsΩ
  have hnonneg (y : Euclidean n) : 0 ≤ χ y*f y := by
    by_cases hy : χ y = 0
    · rw [hy,zero_mul]
    · exact mul_nonneg χ.nonneg ((hball (hs (subset_tsupport χ hy))).2.le)
  have hne : (fun y => χ y*f y) x ≠ 0 := by
    dsimp only
    rw [χ.one_of_mem_closedBall (mem_closedBall_self (by dsimp only [χ]; positivity)),one_mul]
    exact hp.ne'
  have hi := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume)
    χ.hasCompactSupport.mul_right hnonneg hne
  have hz := ht φ (fun y => χ.nonneg) χ.hasCompactSupport hsΩ
  exact (ne_of_gt hi) hz

theorem continuous_zero_of_nonnegative_tests {n : ℕ} {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) {f : Euclidean n → ℝ} (hf : ContinuousOn f Ω)
    (ht : ∀ φ : Euclidean n →ᵇ ℝ, (∀ y, 0 ≤ φ y) →
      HasCompactSupport (φ : Euclidean n → ℝ) → tsupport φ ⊆ Ω →
      (∫ y, φ y*f y) = 0) : EqOn f 0 Ω := by
  have hle := continuous_nonpos_of_nonnegative_tests hΩ hf ht
  have hge := continuous_nonpos_of_nonnegative_tests hΩ hf.neg (fun φ hφ hφc hs => by
    simp only [Pi.neg_apply,mul_neg,integral_neg,ht φ hφ hφc hs,neg_zero])
  intro x hx
  have hl := hle x hx
  have hg := hge x hx
  change -f x ≤ 0 at hg
  change f x = 0
  linarith

end RegularPointCoordinates

end

end OAI
