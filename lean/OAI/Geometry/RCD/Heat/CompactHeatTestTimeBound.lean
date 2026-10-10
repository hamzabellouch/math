import OAI.Geometry.RCD.Heat.CompactHeatMeanTimeBound
import OAI.Geometry.RCD.Heat.CompactHeatInterpolationLaws
import OAI.Geometry.RCD.Sobolev.CompactLipschitzTests

namespace OAI

/-! # Uniform time bounds for compact Lipschitz law tests -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolationLaw_test_lipschitz (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R δ : ℝ} (hR : 0 ≤ R)
    (hS : ∀ y:S, dist z y ≤ R) (hT : ∀ y:T, dist z y ≤ R) (hδ : 0 < δ)
    (φ : X →ᵇ ℝ) {A : ℝ≥0} (hφ : LipschitzWith A φ) (hφc : HasCompactSupport φ) :
    ∃ L : ℝ≥0, ∀ k, LipschitzOnWith L
      (fun t : Ioo (0:ℝ) 1 => ∫ x, φ x ∂(D.interpolationLaw k t : Measure X))
      {t | δ ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-δ} := by
  let m := hausdorff n X
  let q := hX.quadratic
  let w := SobolevSpace.ofLipschitzCompact m q hφ hφc
  have hw : SobolevSpace.toLp m q w =ᵐ[m] φ := SobolevSpace.ofLipschitzCompact_coe m q hφ hφc
  obtain ⟨r,hr⟩ := hφc.isBounded.subset_closedBall z
  have hb : ∀ᵐ x ∂m, |SobolevSpace.toLp m q w x| ≤ ‖φ‖₊ := by
    filter_upwards [hw] with x hx
    rw [hx]
    exact φ.norm_coe_le_norm x
  have hz : ∀ᵐ x ∂m, x ∉ closedBall z r → SobolevSpace.toLp m q w x = 0 := by
    filter_upwards [hw] with x hx hn
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport (fun h => hn (hr h))
  obtain ⟨L,hL⟩ := D.interpolationMean_uniform_lipschitz hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z hR hS hT hδ w ‖φ‖₊ A hb
    (SobolevSpace.ofLipschitzCompact_minimalSlope_le_lip m q hφ hφc) hz
  have he (k : ℕ) (t : Ioo (0:ℝ) 1) :
      (∫ x, φ x ∂(D.interpolationLaw k t : Measure X)) =
        D.interpolationMean (SobolevSpace.toLp m q w) k t := by
    rw [D.interpolationLaw_integral,D.interpolationMean_eq_density]
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    rw [hx,mul_comm]
  refine ⟨L,fun k => LipschitzOnWith.of_dist_le_mul (fun s hs t ht => ?_)⟩
  rw [he,he]
  exact (hL k).dist_le_mul s hs t ht

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
