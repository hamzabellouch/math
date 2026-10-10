import OAI.Geometry.RCD.Metric.EuclideanBoundaryLayerLimit
import OAI.Geometry.RCD.Harmonic.HarmonicBoundaryUniqueness

namespace OAI

/-! # The actual harmonic replacement retains harmonic boundary data -/

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem CompactHarmonicBoundaryLimit.eq_harmonic_boundary {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hn : 2≤n)
    {p : ℕ → X} {r ε : ℕ → ℝ} {V : ℕ → X → Euclidean n} {S R : ℝ} {ψ : Euclidean n → ℝ}
    (d : CompactHarmonicBoundaryLimit hX p r V S R ψ)
    (hS : 0<S) (hR : 0<R) (hRS : R<S)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*(S*r k)^2)
    (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (hψ : InteriorSmoothTest n S ψ) (hψh : HarmonicOnNhd ψ (ball 0 R)) :
    EqOn d.value ψ (ball 0 R) := by
  obtain ⟨M,hM⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψ.2.1 hψ.1 (by simp)
  obtain ⟨A,hA,hbound⟩ := d.truncated_layer_bound hn hS hR hRS.le hr hcurv hε hεlim hV hM
  let η := min (R/4) ((S-R)/2)
  have hη : 0<η := lt_min (by positivity) (by linarith)
  have hv : 0<volume.real (ball (0:Euclidean n) S) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 hS).ne' measure_ball_ne_top
  have hlayer : ∀ δ : ℝ, 0<δ → δ<η → ∀ b : ℝ, R-δ<b → b<R →
      (∫ x in ball (0:Euclidean n) b \ ball 0 (R-δ), (d.value x-ψ x)^2)≤
        (volume.real (ball (0:Euclidean n) S)*A)*δ^2 := by
    intro δ hδ hδη b hab hbR
    have hδR : 4*δ≤R := by have h := hδη.trans_le (min_le_left _ _); linarith
    have hδS : R+2*δ≤S := by have h := hδη.trans_le (min_le_right _ _); linarith
    have hb := hbound δ hδ hδR hδS b hab hbR
    have hm := mul_le_mul_of_nonneg_left hb hv.le
    simpa only [← mul_assoc,mul_inv_cancel₀ hv.ne',one_mul] using hm
  have hz := harmonic_zero_of_squared_boundary_layer (by omega : 0<n) hR
    (d.smooth.sub hψ.1.contDiffOn)
    (fun x hx => ((continuous_weak_harmonic d.continuous d.weak x hx).sub (hψh x hx)).2.self_of_nhds)
    hη hlayer
  intro x hx
  have he := hz hx
  change d.value x-ψ x=0 at he
  exact sub_eq_zero.mp he

end RegularPointCoordinates

end

end OAI
