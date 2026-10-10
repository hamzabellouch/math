import OAI.Geometry.RCD.Transport.CurvatureMidpointLimit

namespace OAI

/-! # The two-source midpoint coefficient tends to one -/

open Filter
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem midpoint_min_coefficient_tendsto_one {K d : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hK : K ≤ 0) {r ε : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -ε k ≤ K*(r k)^2) :
    Tendsto (fun k => (2*midpointFloor K n (d*r k)).toReal^n) atTop (𝓝 1) := by
  have hh := ((midpointFloor_real_tendsto_half hn hK hr hε hcurv (d := d)).const_mul 2).pow n
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,
    show (2:ℝ)*(1/2)=1 by norm_num,one_pow] using hh

end RegularPointCoordinates

end

end OAI
