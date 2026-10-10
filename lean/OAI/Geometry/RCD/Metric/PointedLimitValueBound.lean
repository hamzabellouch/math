import OAI.Geometry.RCD.Metric.ExpandingPointedValueLimit

namespace OAI

/-! # Passing local value bounds to a pointed function limit -/

open Set Metric Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_limit_value_bound {n : ℕ} {R A : ℝ}
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hεlim : Tendsto ε atTop (𝓝 0)) (u : ℕ → X → ℝ) (f : Euclidean n → ℝ)
    (hfc : Continuous f)
    (hdata : ∀ᶠ k in atTop, IsPointedApproximation (p k) 0 (r k) R (ε k) (V k) ∧
      ∀ x, dist x (p k) ≤ R*r k → |u k x| ≤ A)
    (hconv : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x, dist x (p k) ≤ R*r k →
      |u k x-f (V k x)| < η) :
    ∀ z ∈ ball (0 : Euclidean n) R, |f z| ≤ A := by
  intro z hz
  have hzR : ‖z‖ < R := by simpa only [mem_ball,dist_zero_right] using hz
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨δ,hδ,hδf⟩ := Metric.continuousAt_iff.mp hfc.continuousAt (η/2) (half_pos hη)
  obtain ⟨k,hk,hconvk,hsmall,hroom⟩ :=
    (hdata.and ((hconv (η/2) (half_pos hη)).and
      ((hεlim.eventually (Iio_mem_nhds hδ)).and
        (hεlim.eventually (Iio_mem_nhds (sub_pos.mpr hzR)))))).exists
  obtain ⟨x,hx,hxz⟩ := hk.1.2.2 z (by rw [dist_zero_right]; linarith)
  have hfclose : |f (V k x)-f z| < η/2 := by
    simpa only [Real.dist_eq] using hδf (hxz.trans_lt hsmall)
  have huclose := hconvk x hx
  have hub := hk.2 x hx
  have htri := abs_sub_le (f z) (f (V k x)) (u k x)
  have hsum := abs_sub_le (f z) (u k x) 0
  rw [sub_zero,sub_zero] at hsum
  rw [abs_sub_comm] at hfclose huclose
  linarith

end RegularPointCoordinates

end

end OAI
