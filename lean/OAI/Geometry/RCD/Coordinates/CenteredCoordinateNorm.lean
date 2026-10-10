import OAI.Geometry.RCD.Coordinates.CoarseFineCoordinateDistance

namespace OAI

/-! # Centered coordinate approximations locate actual source preimages -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] {n : ℕ}

theorem centered_coordinate_norm_bounds {p : X} {r S ε : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) {v : X → Euclidean n}
    (hV : IsPointedApproximation p 0 r S ε (fun x => r⁻¹ • (v x-v p)))
    {x : X} (hx : dist x p ≤ S*r) :
    dist x p-r*ε ≤ ‖v x-v p‖ ∧ ‖v x-v p‖ ≤ dist x p+r*ε := by
  have hh := hV.2.1 x p hx (by simpa only [dist_self] using mul_nonneg hS hr.le)
  simp only [sub_self,smul_zero,dist_zero_right,norm_smul,
    Real.norm_of_nonneg (inv_pos.mpr hr).le] at hh
  have hs := mul_le_mul_of_nonneg_left hh hr.le
  have habs : |r*(r⁻¹*‖v x-v p‖-dist x p/r)| ≤ r*ε := by
    rw [abs_mul,abs_of_pos hr]
    exact hs
  have he : r*(r⁻¹*‖v x-v p‖-dist x p/r) = ‖v x-v p‖-dist x p := by field_simp
  rw [he] at habs
  exact ⟨by linarith only [(abs_le.mp habs).1],by linarith only [(abs_le.mp habs).2]⟩

theorem centered_coordinate_preimage_ball {p : X} {r S ε ρ e : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) (he : r*ε ≤ e) {v : X → Euclidean n}
    (hV : IsPointedApproximation p 0 r S ε (fun x => r⁻¹ • (v x-v p)))
    {x : X} (hx : dist x p ≤ S*r) (himage : v x-v p ∈ ball 0 ρ) :
    x ∈ ball p (ρ+e) := by
  have hn := (centered_coordinate_norm_bounds hr hS hV hx).1
  have hi : ‖v x-v p‖ < ρ := by simpa only [mem_ball,dist_zero_right] using himage
  exact mem_ball.mpr (by linarith only [hn,hi,he])

end RegularPointCoordinates

end

end OAI
