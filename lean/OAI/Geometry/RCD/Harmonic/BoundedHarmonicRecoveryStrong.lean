import OAI.Geometry.RCD.Sobolev.BoundedHarmonicScaledEnergy
import OAI.Geometry.RCD.Harmonic.HarmonicRecoveryStrong

namespace OAI

/-! # Strong local recovery for the actual bounded harmonic coordinates -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_harmonic_recovery_strong {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S a b R T Q M : ℝ} (hS : 0<S) (ha : 0<a) (hab : a<b) (hbR : b<R)
    (hRT : R<T) (hTS : T<S) (hM : 0<M)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (w q : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤M)
    (g F : Euclidean n → ℝ)
    (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (heq : EqOn F g (closedBall 0 T))
    (hd : EqOn (fderiv ℝ F) (fderiv ℝ g) (ball 0 T))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (V k x)|≤δ)
    (hqconv : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k) x-F (V k x)|≤δ)
    (hqg : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r k^2*localGamma (hausdorff n X) hX.quadratic (q k) (q k) x≤Q^2)
    (hq : Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), (euclideanNestedCutoff n hab (V k x))^2*
        localGamma (hausdorff n X) hX.quadratic (q k) (q k) x ∂hausdorff n X)
      atTop (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
        ∫ z in ball 0 S, (euclideanNestedCutoff n hab z)^2*‖fderiv ℝ F z‖^2))) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (R*r k), (nestedBallCutoff (p k) (a*r k) (b*r k) x)^2*
        localGamma (hausdorff n X) hX.quadratic (w k-q k) (w k-q k) x ∂hausdorff n X)
      atTop (𝓝 0) := by
  obtain ⟨B,hB,hwb⟩ := hX.bounded_harmonic_scaled_energy_bound hn hS
    (ha.le.trans (hab.le.trans (hbR.le.trans hRT.le))) hTS hM p r hr hcurv w hw hnorm
  exact hX.harmonic_recovery_strong_of_gradient_bound hn hS ha hab hbR hRT hTS
    p r ε V hr hcurv hε hε1 hεlim hV w q hw hB hwb g F hg heq hd hconv hqconv hqg hq

end RegularPointCoordinates

end

end OAI
