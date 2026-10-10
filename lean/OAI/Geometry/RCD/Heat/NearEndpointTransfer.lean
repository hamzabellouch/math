import OAI.Geometry.RCD.Heat.NearbyHeatEndpoint

namespace OAI

/-! # Transfer of a normalized endpoint estimate to nearby points -/

open Metric
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem near_endpoint_transfer (φ : X → ℝ) (v : X → Y) (x y x' y' : X)
    {r δ H C F E : ℝ} (hr : 0<r) (hH : 0≤H) (hC : 0≤C) (hF : 0≤F)
    (hnear : dist x' x+dist y' y≤δ*r)
    (hφx : dist (φ x') (φ x)≤H*dist x' x)
    (hφy : dist (φ y') (φ y)≤H*dist y' y)
    (hvx : dist (v x') (v x)≤C*dist x' x)
    (hvy : dist (v y') (v y)≤C*dist y' y)
    (hb : |φ y'-φ x'|/r≤F*(dist (v x') (v y')/r)+E) :
    |φ y-φ x|/r≤F*(dist (v x) (v y)/r)+E+(H+F*C)*δ := by
  have hφ : |φ y-φ x|≤|φ y'-φ x'|+H*(dist x' x+dist y' y) := by
    have hh := dist_triangle4 (φ y) (φ y') (φ x') (φ x)
    rw [dist_comm (φ y) (φ y')] at hh
    simp only [Real.dist_eq] at hh hφx hφy
    linarith
  have hv : dist (v x') (v y')≤dist (v x) (v y)+C*(dist x' x+dist y' y) := by
    have hh := dist_triangle4 (v x') (v x) (v y) (v y')
    rw [dist_comm (v y) (v y')] at hh
    linarith
  have hn : (dist x' x+dist y' y)/r≤δ := (div_le_iff₀ hr).mpr hnear
  have hs := div_le_div_of_nonneg_right hφ hr.le
  have hv' := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hv hr.le) hF
  have hmul := mul_le_mul_of_nonneg_left hn (add_nonneg hH (mul_nonneg hF hC))
  calc
    _≤|φ y'-φ x'|/r+H*((dist x' x+dist y' y)/r) := by
      convert hs using 1
      ring
    _≤F*(dist (v x') (v y')/r)+E+H*((dist x' x+dist y' y)/r) :=
      add_le_add hb le_rfl
    _≤F*(dist (v x) (v y)/r)+E+(H+F*C)*((dist x' x+dist y' y)/r) := by
      convert add_le_add hv' (le_refl (E+H*((dist x' x+dist y' y)/r))) using 1 <;> ring
    _≤_ := add_le_add le_rfl hmul

end RegularPointCoordinates

end

end OAI
