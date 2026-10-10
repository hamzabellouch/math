import OAI.Geometry.RCD.Harmonic.WeightedDirectionalBound
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! # Vanishing from the weighted directional Young estimate -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

/-- The dominating mass and the directional bound stay fixed as the
weighted directional energy tends uniformly to zero. -/
theorem tendstoUniformly_of_directional_bound {Y : Type*} {A E : ℕ → Y → ℝ}
    {C M : ℝ} (hC : 0≤C) (hM : 0≤M)
    (hA : ∀ k y, 0≤A k y)
    (hE : TendstoUniformly E (fun _ => 0) atTop)
    (hb : ∀ k y r, 0<r → 4*r*A k y ≤ 4*r^2*C+M*E k y) :
    TendstoUniformly A (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  let r := e/(4*(C+1))
  have hr : 0<r := div_pos he (by positivity)
  have hre : 4*r*(C+1)=e := by
    dsimp only [r]
    field_simp
  let η := r*e/(M+1)
  have hη : 0<η := div_pos (mul_pos hr he) (by positivity)
  have hηe : η*(M+1)=r*e := by
    dsimp only [η]
    field_simp
  filter_upwards [(Metric.tendstoUniformly_iff.mp hE) η hη] with k hk y
  have hEk : E k y<η := by
    have hh := hk y
    simp only [dist_zero_left,Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans_lt hh
  have hME : M*E k y≤M*η := mul_le_mul_of_nonneg_left hEk.le hM
  have hbound := hb k y r hr
  have hsmall : A k y<e := by
    nlinarith [mul_pos hr he]
  simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (hA k y)] using hsmall

end RegularPointCoordinates

end

end OAI
