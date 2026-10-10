import OAI.Geometry.RCD.Harmonic.MeasuredRadialL2
import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # Compact radial weights agree on the gradients of supported recoveries -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem compact_radial_pullback (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} {S c T : ℝ} (hS : 0<S) (hcT : c<T) (hTS : T<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (V k))
    (u w : ℕ → SobolevSpace μ hQ)
    (hz : ∀ k, ∀ᵐ x ∂μ, x∉ball (p k) (c*r k) → SobolevSpace.toLp μ hQ (u k) x=0)
    (F : Euclidean n →ᵇ ℝ) (hF : EqOn F (fun z => ‖z‖^2/2) (closedBall 0 T)) :
    ∀ᶠ k in atTop, (fun x => (‖V k x‖^2/2)*localGamma μ hQ (u k) (w k) x)=ᵐ[μ]
      (fun x => F (V k x)*localGamma μ hQ (u k) (w k) x) := by
  filter_upwards [hε.eventually (gt_mem_nhds (show 0<(T-c)/2 by linarith))] with k hk
  filter_upwards [hz k,localGamma_zero_on_level μ hQ (u k) (w k) 0] with x hx hγ
  by_cases hxc : x∈ball (p k) (c*r k)
  · have hxs : dist x (p k)≤S*r k :=
      hxc.le.trans (mul_le_mul_of_nonneg_right (hcT.trans hTS).le (hr k).le)
    have hd := (abs_le.mp (pointed_radial_distance (hr k) hS.le (hV k).metric hxs)).2
    have hdc : dist x (p k)/r k<c := (div_lt_iff₀ (hr k)).mpr hxc
    have hnorm : V k x∈closedBall (0:Euclidean n) T := by
      rw [mem_closedBall,dist_zero_right]
      linarith
    rw [hF hnorm]
  · rw [hγ (hx hxc),mul_zero,mul_zero]

end RegularPointCoordinates

end

end OAI
