import OAI.Geometry.RCD.Transport.PointedHopfMinimizer

namespace OAI

/-! # Local slope control of the actual metric Hopf--Lax recovery -/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem pointed_hopf_slope_bound {n : ℕ} {p x : X} {r S ρ ε t e : ℝ}
    (hr : 0<r) (ht : 0<t) (hε : 0≤ε) (he0 : 0≤e) {M L : ℝ≥0}
    (hρ : 0≤ρ) (hroom : ρ+2*t*(M:ℝ)+3*ε≤S)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {F : X → ℝ} {ψ : Euclidean n → ℝ}
    (hF : LipschitzWith ⟨(M:ℝ)/r,div_nonneg M.coe_nonneg hr.le⟩ F)
    (hψ : LipschitzWith M ψ)
    (he : ∀ z, dist z p≤S*r → |F z-ψ (v z)|≤e)
    (hx : dist x p≤ρ*r)
    (hlocal : LipschitzOnWith L ψ (closedBall (v x) (2*t*(M:ℝ)+ε))) :
    r*(localSlope (hopfLax F (t*r^2)) x).toReal ≤
      (L:ℝ)+(Real.sqrt (2*t*pointedHopfError t M ε e)+ε)/t := by
  let T := t*r^2
  have hT : 0<T := mul_pos ht (sq_pos_of_pos hr)
  obtain ⟨y,hy,hR⟩ := hopfRadius_attained hF hT x
  have hres := pointed_hopf_minimizer_cost hr ht hε hρ hroom hv hF hψ he hx hy
  have hE : 0≤pointedHopfError t M ε e := pointedHopfError_nonneg ht M.coe_nonneg hε he0
  have hloc : LipschitzOnWith L ψ (closedBall (v x) (dist (v y) (v x))) := by
    apply hlocal.mono (closedBall_subset_closedBall _)
    simpa only [dist_comm] using hres.2.1
  have hrad := approximate_hopf_minimizer_radius hψ ht hE (v x) (v y) hloc hres.2.2
  have hxS : dist x p≤S*r := by
    apply hx.trans (mul_le_mul_of_nonneg_right _ hr.le)
    nlinarith [mul_nonneg ht.le M.coe_nonneg]
  have hmetric := (abs_le.mp (hv.2.1 x y hxS hres.1)).1
  have hRbound : hopfRadius F T x/r≤
      t*(L:ℝ)+Real.sqrt (2*t*pointedHopfError t M ε e)+ε := by
    rw [dist_comm (v y) (v x)] at hrad
    rw [hR]
    linarith
  have hs := hopfLax_slope_le hF hT x
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  have hs' := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mpr hs
  rw [ENNReal.toReal_ofReal (div_nonneg (hopfRadius_bounds hF hT x).1 hT.le)] at hs'
  calc
    r*(localSlope (hopfLax F (t*r^2)) x).toReal ≤r*(hopfRadius F T x/T) :=
      mul_le_mul_of_nonneg_left hs' hr.le
    _ = (hopfRadius F T x/r)/t := by dsimp only [T]; field_simp
    _ ≤ (t*(L:ℝ)+Real.sqrt (2*t*pointedHopfError t M ε e)+ε)/t :=
      div_le_div_of_nonneg_right hRbound ht.le
    _ = (L:ℝ)+(Real.sqrt (2*t*pointedHopfError t M ε e)+ε)/t := by field_simp; ring

end RegularPointCoordinates

end

end OAI
