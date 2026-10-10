import OAI.Geometry.RCD.Harmonic.NearColumnNorm
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! # A column estimate on nearby endpoints controls their actual distance -/

open Metric
open scoped InnerProductSpace
namespace RegularPointCoordinates

theorem near_column_distance {X E : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : X → E) (x y x' y' : X) {C δ r e : ℝ}
    (hC : 0≤C) (hr : 0<r) (he : 0≤e)
    (hnear : dist x' x+dist y' y≤δ*r)
    (hvx : dist (v x') (v x)≤C*dist x' x)
    (hvy : dist (v y') (v y)≤C*dist y' y)
    (hcol : ⟪v y'-v x',v y-v x⟫_ℝ^2≤
      (dist x' y')^2*‖v y-v x‖^2*(1+e)) :
    dist (v x) (v y)/r ≤
      (dist x y/r+δ)*Real.sqrt (1+e)+C*δ := by
  have hn : ‖(v y-v x)-(v y'-v x')‖≤C*(δ*r) := by
    calc
      _=‖(v y-v y')-(v x-v x')‖ := by congr 1; abel
      _≤‖v y-v y'‖+‖v x-v x'‖ := norm_sub_le _ _
      _≤C*dist y' y+C*dist x' x := by
        simpa only [← dist_eq_norm,dist_comm] using add_le_add hvy hvx
      _≤C*(δ*r) := by nlinarith
  have hb := near_column_norm (v y'-v x') (v y-v x) dist_nonneg he hn hcol
  have hd : dist x' y'≤dist x y+δ*r := by
    have hh := dist_triangle4 x' x y y'
    rw [dist_comm y y'] at hh
    linarith
  have hv : dist (v x) (v y)≤(dist x y+δ*r)*Real.sqrt (1+e)+C*(δ*r) := by
    rw [dist_eq_norm, norm_sub_rev]
    exact hb.trans (add_le_add
      (mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg _)) le_rfl)
  apply (div_le_iff₀ hr).mpr
  calc
    _≤(dist x y+δ*r)*Real.sqrt (1+e)+C*(δ*r) := hv
    _=((dist x y/r+δ)*Real.sqrt (1+e)+C*δ)*r := by field_simp

end RegularPointCoordinates

end OAI
