import OAI.Geometry.RCD.Transport.PointedHopfLaxLower

namespace OAI

/-! # Upper convergence bound using the density of the prescribed approximation -/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem pointed_hopfLax_upper {n : ℕ} {p x : X} {r S ρ ε t e : ℝ}
    (hr : 0<r) (ht : 0<t) (hε : 0≤ε) {M : ℝ≥0}
    (hρ : 0≤ρ) (hroom : ρ+2*t*(M:ℝ)+3*ε≤S)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {F : X → ℝ} {ψ : Euclidean n → ℝ}
    (hF : LipschitzWith ⟨(M:ℝ)/r,div_nonneg M.coe_nonneg hr.le⟩ F)
    (hψ : LipschitzWith M ψ)
    (he : ∀ y, dist y p≤S*r → |F y-ψ (v y)|≤e)
    (hx : dist x p≤ρ*r) :
    hopfLax F (t*r^2) x ≤ hopfLax ψ t (v x)+e+(M:ℝ)*ε+
      (2*ε)*(4*t*(M:ℝ)+2*ε)/(2*t) := by
  have hS : 0≤S := by nlinarith [mul_nonneg ht.le M.coe_nonneg]
  have hxS : dist x p≤S*r := by
    apply hx.trans (mul_le_mul_of_nonneg_right _ hr.le)
    nlinarith [mul_nonneg ht.le M.coe_nonneg]
  have hxn : ‖v x‖≤ρ+2*ε := by
    have ht' := (abs_le.mp (pointed_radial_distance hr hS hv hxS)).2
    have hxr := (div_le_iff₀ hr).mpr hx
    linarith
  obtain ⟨z,hz,hzd⟩ := hopfLax_exists_minimizer hψ ht (v x)
  have hzS : dist z (0:Euclidean n)≤S-ε := by
    rw [dist_zero_right]
    have htri := dist_triangle z (v x) 0
    rw [dist_comm z (v x),dist_zero_right,dist_zero_right] at htri
    linarith
  obtain ⟨y,hyS,hyz⟩ := hv.2.2 z hzS
  have hD : |dist x y/r-dist (v x) z|≤2*ε := by
    have hm := abs_le.mp (hv.2.1 x y hxS hyS)
    have h₁ := dist_triangle (v x) (v y) z
    have h₂ := dist_triangle (v x) z (v y)
    rw [dist_comm z (v y)] at h₂
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hsq := (abs_le.mp (sq_error_of_abs_sub_le
    (div_nonneg dist_nonneg hr.le) dist_nonneg hzd (show 0≤2*ε by positivity) hD)).2
  have hc : (dist x y/r)^2/(2*t)≤dist (v x) z^2/(2*t)+
      (2*ε)*(4*t*(M:ℝ)+2*ε)/(2*t) := by
    have hh := div_le_div_of_nonneg_right hsq (show 0≤2*t by positivity)
    rw [sub_div] at hh
    ring_nf at hh ⊢
    linarith only [hh]
  have hψdiff : ψ (v y)≤ψ z+(M:ℝ)*ε := by
    have hd := (le_abs_self (ψ (v y)-ψ z)).trans (hψ.dist_le_mul (v y) z)
    have hm := mul_le_mul_of_nonneg_left hyz M.coe_nonneg
    linarith
  have hFdiff := (abs_le.mp (he y hyS)).2
  have hcost := hopfLax_le_cost hF (mul_pos ht (sq_pos_of_pos hr)) x y
  rw [scaled_quadratic_cost ht hr] at hcost
  rw [hz]
  linarith

end RegularPointCoordinates

end

end OAI
