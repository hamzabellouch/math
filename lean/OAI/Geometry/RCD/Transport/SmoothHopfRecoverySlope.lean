import OAI.Geometry.RCD.Transport.PointedHopfErrorLimit
import OAI.Geometry.RCD.Sobolev.SmoothLocalLipschitz

namespace OAI

/-! # The recovered local slopes approach the differential of the Euclidean test -/

open Set Metric Filter
open scoped ContDiff Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem smooth_hopf_recovery_slope {n : ℕ} {ψ : Euclidean n → ℝ} {M : ℝ≥0}
    (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) (hψL : LipschitzWith M ψ)
    {S ρ η : ℝ} (hρ : 0≤ρ) (hη : 0<η)
    (p : ℕ → X) (r ε e : ℕ → ℝ) (v : ℕ → X → Euclidean n) (F : ℕ → X → ℝ)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (he : ∀ k, 0≤e k)
    (hεlim : Tendsto ε atTop (𝓝 0)) (helim : Tendsto e atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hF : ∀ k, LipschitzWith ⟨(M:ℝ)/r k,div_nonneg M.coe_nonneg (hr k).le⟩ (F k))
    (hFe : ∀ k x, dist x (p k)≤S*r k → |F k x-ψ (v k x)|≤e k) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, 0<t → ρ+2*t*(M:ℝ)<S → 2*t*(M:ℝ)<δ →
      ∀ᶠ k in atTop, ∀ x : X, dist x (p k)≤ρ*r k →
        r k*(localSlope (hopfLax (F k) (t*(r k)^2)) x).toReal≤
          ‖fderiv ℝ ψ (v k x)‖+η := by
  obtain ⟨δ,hδ,hlocal⟩ := compact_smooth_local_lipschitz hψ hs (half_pos hη)
  refine ⟨δ,hδ,?_⟩
  intro t ht hroom hsmall
  have hslope := (pointedHopfSlopeError_tendsto (t:=t) (M:=M) hεlim helim).eventually
    (Iio_mem_nhds (half_pos hη))
  have hεsmall := hεlim.eventually (Iio_mem_nhds (show 0<δ-2*t*(M:ℝ) by linarith))
  have hεroomlim : Tendsto (fun k => 3*ε k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hεlim.const_mul 3
  have hεroom := hεroomlim.eventually
    (Iio_mem_nhds (show 0<S-ρ-2*t*(M:ℝ) by linarith))
  filter_upwards [hslope,hεsmall,hεroom] with k hk hks hkr
  intro x hx
  let L : ℝ≥0 := ‖fderiv ℝ ψ (v k x)‖₊+⟨η/2,(half_pos hη).le⟩
  have hloc : LipschitzOnWith L ψ (closedBall (v k x) (2*t*(M:ℝ)+ε k)) :=
    (hlocal (v k x)).mono (closedBall_subset_closedBall (by linarith))
  have hb := pointed_hopf_slope_bound (hr k) ht (hε k) (he k) hρ (by linarith)
    (hv k) (hF k) hψL (hFe k) hx hloc
  change r k*(localSlope (hopfLax (F k) (t*(r k)^2)) x).toReal≤
    ‖fderiv ℝ ψ (v k x)‖+η/2+
      (Real.sqrt (2*t*pointedHopfError t M (ε k) (e k))+ε k)/t at hb
  linarith

end RegularPointCoordinates

end

end OAI
