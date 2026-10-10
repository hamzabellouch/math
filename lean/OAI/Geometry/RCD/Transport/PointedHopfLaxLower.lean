import OAI.Geometry.RCD.Coordinates.QuadraticMetricError
import OAI.Analysis.RCDHeat.HopfHeat

namespace OAI

/-! # Lower convergence bound for the actual Hopf--Lax recovered tests -/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem pointed_hopfLax_lower {n : ℕ} {p x : X} {r S ρ ε t e : ℝ}
    (hr : 0<r) (ht : 0<t) (hε : 0≤ε) {M : ℝ≥0}
    (hroom : ρ+2*t*(M:ℝ)≤S)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {F : X → ℝ} {ψ : Euclidean n → ℝ}
    (hF : LipschitzWith ⟨(M:ℝ)/r,div_nonneg M.coe_nonneg hr.le⟩ F)
    (hψ : LipschitzWith M ψ)
    (he : ∀ y, dist y p≤S*r → |F y-ψ (v y)|≤e)
    (hx : dist x p≤ρ*r) :
    hopfLax ψ t (v x)-e-ε*(4*t*(M:ℝ)+ε)/(2*t) ≤
      hopfLax F (t*r^2) x := by
  have hT : 0<t*r^2 := mul_pos ht (sq_pos_of_pos hr)
  obtain ⟨y,hy,hdy⟩ := hopfLax_exists_minimizer hF hT x
  have hdyr : dist x y/r≤2*t*(M:ℝ) := by
    apply (div_le_iff₀ hr).mpr
    change dist x y≤2*(t*r^2)*((M:ℝ)/r) at hdy
    convert hdy using 1
    field_simp
  have hyS : dist y p≤S*r := by
    have htri := dist_triangle y x p
    rw [dist_comm y x] at htri
    have hd := (div_le_iff₀ hr).mp hdyr
    have hm := mul_le_mul_of_nonneg_right hroom hr.le
    nlinarith
  have hxS : dist x p≤S*r := by
    apply hx.trans
    apply mul_le_mul_of_nonneg_right _ hr.le
    linarith [mul_nonneg ht.le M.coe_nonneg]
  have hcost := pointed_square_distance_error hr hε hv hxS hyS hdyr
  have hcost' := (abs_le.mp hcost).2
  have hc : dist (v x) (v y)^2/(2*t)≤(dist x y/r)^2/(2*t)+
      ε*(4*t*(M:ℝ)+ε)/(2*t) := by
    have hh := div_le_div_of_nonneg_right hcost' (show 0≤2*t by positivity)
    rw [sub_div] at hh
    ring_nf at hh ⊢
    linarith only [hh]
  have hh := hopfLax_le_cost hψ ht (v x) (v y)
  have hf := (abs_le.mp (he y hyS)).1
  rw [hy,scaled_quadratic_cost ht hr]
  linarith

end RegularPointCoordinates

end

end OAI
