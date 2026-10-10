import OAI.Geometry.RCD.Sobolev.PointedEnergyCompactness
import OAI.Geometry.RCD.Sobolev.HarmonicScaledEnergy

namespace OAI

/-! # Actual harmonic sequences have bounded Euclidean energy-measure limits -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.harmonic_energy_subsequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S R : ℝ} (hS : 0<S) (hR : 0≤R) (hRS : R<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤1) :
    ∃ M : ℝ, 0≤M ∧ ∃ ν : FiniteMeasure (Euclidean n), ∃ t : ℕ → ℕ, StrictMono t ∧
      Tendsto (fun k => (localEnergyMeasure (hausdorff n X) hX.quadratic (w (t k))
        (closedBall (p (t k)) (R*r (t k)))
        (r (t k)^2/(hausdorff n X).real (ball (p (t k)) (S*r (t k))))).map (v (t k)))
        atTop (𝓝 ν) ∧
      (ν : Measure (Euclidean n))≤ENNReal.ofReal M •
        (euclideanBallProbability n S : Measure (Euclidean n)) := by
  let : ProperSpace X := hX.proper K n hn
  obtain ⟨M,hM,hb⟩ := hX.harmonic_scaled_energy_bound hn hS hR hRS p r hr hcurv w hw hnorm
  exact ⟨M,hM,hX.pointed_energy_subsequence hS hR hRS hM p r ε v hr hε1 hεlim hv w hb⟩

end RegularPointCoordinates

end

end OAI
