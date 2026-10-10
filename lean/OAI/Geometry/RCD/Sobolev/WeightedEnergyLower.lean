import OAI.Geometry.RCD.Sobolev.UniformEnergyDensity
import OAI.Geometry.RCD.Sobolev.PointedEnergyCompactness
import OAI.Geometry.RCD.Sobolev.WeightedGradientDensity
import OAI.Geometry.RCD.Sobolev.WeightedEnergyMap

namespace OAI

/-! # Sharp lower bounds for compactly weighted energies

The weight is an actual test on the prescribed approximation maps. The
subsequence uses the same positive energy measures as the unweighted proof.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem euclideanBallProbability_absolutelyContinuous {n : ℕ} {S : ℝ} (hS : 0<S) :
    (euclideanBallProbability n S : Measure (Euclidean n)) ≪ volume := by
  let : IsFiniteMeasure ((volume : Measure (Euclidean n)).restrict (ball 0 S)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := (volume : Measure (Euclidean n))) (x := 0) (r := S))⟩
  have hn : (volume : Measure (Euclidean n)).restrict (ball 0 S)≠0 := by
    intro he
    have hh := congrArg (fun μ : Measure (Euclidean n) => μ univ) he
    simp only [Measure.restrict_apply_univ,Measure.coe_zero,Pi.zero_apply] at hh
    exact (measure_ball_pos volume 0 hS).ne' hh
  change (normalizedProbabilityLaw (volume.restrict (ball (0:Euclidean n) S)) :
    Measure (Euclidean n)) ≪ volume
  rw [normalizedProbabilityLaw_measure _ hn]
  exact Measure.absolutelyContinuous_restrict.smul_left _

theorem NoncollapsedRCD.weighted_energy_lower_of_curvature_sequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S ρ τ R : ℝ} (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (hτR : τ<R) (hRS : R<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g : Euclidean n → ℝ) (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤δ)
    (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0≤φ z) (hs : Function.support φ⊆ball 0 ρ)
    {M C : ℝ} (hM : 0≤M)
    (hbound : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M)
    (hupper : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      (r k^2/(hausdorff n X).real (ball (p k) (S*r k)))*
        (∫ x in closedBall (p k) (R*r k), φ (v k x)*localGamma (hausdorff n X) hX.quadratic
          (w k) (w k) x ∂hausdorff n X)≤C+δ) :
    Integrable (fun z => φ z*‖fderiv ℝ g z‖^2) volume ∧
      (∫ z, φ z*‖fderiv ℝ g z‖^2)≤volume.real (ball (0:Euclidean n) S)*C := by
  obtain ⟨ν,t,ht,hweak,hdom⟩ := hX.pointed_energy_subsequence hS (hτ.trans hτR.le) hRS hM
    p r ε v hr hε1 hεlim hv w hbound
  have hconv' (W : ℝ) (hW : 0<W) (hWS : W<S) (δ : ℝ) (hδ : 0<δ) :=
    ht.tendsto_atTop.eventually (hconv W hW hWS δ hδ)
  have hdensity := hX.uniform_energy_density_dominates_gradient hn hS hτ hρτ hτR hRS
    (p ∘ t) (r ∘ t) (ε ∘ t) (v ∘ t) (fun k => hr (t k))
    (fun k => hcurv (t k)) (fun k => hε (t k)) (fun k => hε1 (t k))
    (hεlim.comp ht.tendsto_atTop) (fun k => hv (t k)) (w ∘ t) g hg hconv' ν hweak
  have hac : (ν : Measure (Euclidean n)) ≪ volume :=
    (Measure.absolutelyContinuous_of_le hdom).trans
      ((euclideanBallProbability_absolutelyContinuous hS).smul_left _)
  have hlow := weighted_gradient_energy_from_density ν g measurableSet_ball hac φ hφ hs hdensity
  have hlim := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak φ
  have hmass : (∫ z, φ z ∂(ν : Measure (Euclidean n)))≤C := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    apply le_of_tendsto hlim
    filter_upwards [ht.tendsto_atTop.eventually (hupper δ hδ)] with k hk
    rw [localEnergyMeasure_map_integral (hausdorff n X) hX.quadratic (w (t k))
      (closedBall (p (t k)) (R*r (t k)))
      (c := r (t k)^2/(hausdorff n X).real (ball (p (t k)) (S*r (t k))))
      (div_nonneg (sq_nonneg (r (t k))) ENNReal.toReal_nonneg) (hv (t k)).measurable φ]
    exact hk
  exact ⟨hlow.1,hlow.2.trans (mul_le_mul_of_nonneg_left hmass ENNReal.toReal_nonneg)⟩

end RegularPointCoordinates

end

end OAI
