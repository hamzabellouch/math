import OAI.MeasureTheory.Falconer.Geometry.ProjectedSeparation

namespace OAI

/-! # Exact distance ratio for a projected original direction -/
namespace Falconer
open NormedSpace
variable {d m k : ℕ}

theorem norm_projected_radialDirection (P : Space d →L[ℝ] Space m) (x y : Space d) :
    ‖P (radialDirection x y)‖ = dist (P x) (P y) / dist x y := by
  rw [radialDirection,map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
    map_sub,← dist_eq_norm,← dist_eq_norm,dist_comm y x,dist_comm (P y) (P x)]
  rw [div_eq_mul_inv,mul_comm]

theorem projected_distance_lower (P : Space d →L[ℝ] Space m) (x y : Space d)
    {r c : ℝ} (hc : 0 ≤ c) (hr : 0 < r) (hxy : r ≤ dist x y)
    (hlower : c ≤ ‖P (radialDirection x y)‖) : c*r ≤ dist (P x) (P y) := by
  rw [norm_projected_radialDirection] at hlower
  have hd : 0 < dist x y := hr.trans_le hxy
  exact (mul_le_mul_of_nonneg_left hxy hc).trans ((le_div_iff₀ hd).mp hlower)

theorem contractive_distance_le (P : Space d →L[ℝ] Space m) (hP : ‖P‖ ≤ 1)
    (x y : Space d) : dist (P x) (P y) ≤ dist x y := by
  exact (P.dist_le_opNorm x y).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hP (dist_nonneg : 0 ≤ dist x y))

end Falconer

end OAI
