import OAI.Geometry.RCD.Transport.SmoothHopfRecoverySlope
import OAI.Geometry.RCD.Transport.HopfRecoveryTime

namespace OAI

/-! # One smoothing sequence with asymptotically sharp local slope bounds -/

open Set Metric Filter
open scoped ContDiff Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem diagonal_hopf_recovery_slope {n : ℕ} {ψ : Euclidean n → ℝ} {M : ℝ≥0}
    (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) (hψL : LipschitzWith M ψ)
    {S ρ : ℝ} (hρ : 0≤ρ) (hρS : ρ<S)
    (p : ℕ → X) (r ε e t : ℕ → ℝ) (v : ℕ → X → Euclidean n) (F : ℕ → X → ℝ)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (he : ∀ k, 0≤e k) (ht : ∀ k, 0<t k)
    (hεlim : Tendsto ε atTop (𝓝 0)) (htlim : Tendsto t atTop (𝓝 0))
    (hεratio : Tendsto (fun k => ε k/t k) atTop (𝓝 0))
    (heratio : Tendsto (fun k => e k/t k) atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hF : ∀ k, LipschitzWith ⟨(M:ℝ)/r k,div_nonneg M.coe_nonneg (hr k).le⟩ (F k))
    (hFe : ∀ k x, dist x (p k)≤S*r k → |F k x-ψ (v k x)|≤e k) :
    ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x : X, dist x (p k)≤ρ*r k →
      r k*(localSlope (hopfLax (F k) (t k*(r k)^2)) x).toReal≤
        ‖fderiv ℝ ψ (v k x)‖+η := by
  intro η hη
  obtain ⟨δ,hδ,hlocal⟩ := compact_smooth_local_lipschitz hψ hs (half_pos hη)
  have hslope := (pointedHopfSlopeError_diagonal_tendsto (M:=M) ht hεratio heratio).eventually
    (Iio_mem_nhds (half_pos hη))
  have hrad : Tendsto (fun k => 2*t k*(M:ℝ)+ε k) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add] using ((htlim.const_mul 2).mul_const (M:ℝ)).add hεlim
  have hroom : Tendsto (fun k => 2*t k*(M:ℝ)+3*ε k) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add] using
      ((htlim.const_mul 2).mul_const (M:ℝ)).add (hεlim.const_mul 3)
  filter_upwards [hslope,hrad.eventually (Iio_mem_nhds hδ),
    hroom.eventually (Iio_mem_nhds (sub_pos.mpr hρS))] with k hk hkr hks
  intro x hx
  let L : ℝ≥0 := ‖fderiv ℝ ψ (v k x)‖₊+⟨η/2,(half_pos hη).le⟩
  have hloc : LipschitzOnWith L ψ (closedBall (v k x) (2*t k*(M:ℝ)+ε k)) :=
    (hlocal (v k x)).mono (closedBall_subset_closedBall hkr.le)
  have hb := pointed_hopf_slope_bound (hr k) (ht k) (hε k) (he k) hρ (by linarith)
    (hv k) (hF k) hψL (hFe k) hx hloc
  change r k*(localSlope (hopfLax (F k) (t k*(r k)^2)) x).toReal≤
    ‖fderiv ℝ ψ (v k x)‖+η/2+
      (Real.sqrt (2*t k*pointedHopfError (t k) M (ε k) (e k))+ε k)/t k at hb
  linarith

end RegularPointCoordinates

end

end OAI
