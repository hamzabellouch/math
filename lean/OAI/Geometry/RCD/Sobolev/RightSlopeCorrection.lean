import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! # A first-order correction retained in a one-sided comparison -/

open Filter Set
open scoped Topology
namespace RegularPointCoordinates

theorem right_slope_correction_le {f g c : ℝ → ℝ} {a b d : ℝ}
    (hf : Tendsto (fun t => (f t-f 0)/t) (𝓝[>] 0) (𝓝 a))
    (hg : Tendsto (fun t => (g t-g 0)/t) (𝓝[>] 0) (𝓝 b))
    (hc : Tendsto c (𝓝[>] 0) (𝓝 d)) (hzero : f 0=g 0)
    (h : ∀ t, 0<t → f t+t*c t≤g t) : a+d≤b := by
  apply le_of_tendsto_of_tendsto (hf.add hc) hg
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0<t)
  have hh := h t ht
  rw [hzero]
  apply (le_div_iff₀ ht).mpr
  rw [add_mul,div_mul_cancel₀ _ ht.ne']
  linarith

end RegularPointCoordinates

end OAI
