import OAI.Geometry.RCD.Metric.EuclideanApproximateMinimizer

namespace OAI

/-! # Actual source minimizers are approximate Euclidean minimizers -/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]

def pointedHopfError (t M ε e : ℝ) : ℝ :=
  2*e+M*ε+(2*ε)*(4*t*M+2*ε)/(2*t)+ε*(4*t*M+ε)/(2*t)

theorem pointedHopfError_nonneg {t M ε e : ℝ}
    (ht : 0<t) (hM : 0≤M) (hε : 0≤ε) (he : 0≤e) :
    0≤pointedHopfError t M ε e := by
  unfold pointedHopfError
  positivity

omit [ProperSpace X] in
theorem pointed_hopf_minimizer_cost {n : ℕ} {p x y : X} {r S ρ ε t e : ℝ}
    (hr : 0<r) (ht : 0<t) (hε : 0≤ε) {M : ℝ≥0}
    (hρ : 0≤ρ) (hroom : ρ+2*t*(M:ℝ)+3*ε≤S)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {F : X → ℝ} {ψ : Euclidean n → ℝ}
    (hF : LipschitzWith ⟨(M:ℝ)/r,div_nonneg M.coe_nonneg hr.le⟩ F)
    (hψ : LipschitzWith M ψ)
    (he : ∀ z, dist z p≤S*r → |F z-ψ (v z)|≤e)
    (hx : dist x p≤ρ*r)
    (hy : hopfLax F (t*r^2) x=F y+dist x y^2/(2*(t*r^2))) :
    dist y p≤S*r ∧ dist (v x) (v y)≤2*t*(M:ℝ)+ε ∧
      ψ (v y)+dist (v x) (v y)^2/(2*t)≤
        hopfLax ψ t (v x)+pointedHopfError t M ε e := by
  have hdy := hopfLax_minimizer_dist hF (mul_pos ht (sq_pos_of_pos hr)) hy
  have hdyr : dist x y/r≤2*t*(M:ℝ) := by
    apply (div_le_iff₀ hr).mpr
    change dist x y≤2*(t*r^2)*((M:ℝ)/r) at hdy
    convert hdy using 1
    field_simp
  have hyS : dist y p≤S*r := by
    have htri := dist_triangle y x p
    rw [dist_comm y x] at htri
    have hd := (div_le_iff₀ hr).mp hdyr
    have hroom' : ρ+2*t*(M:ℝ)≤S := by linarith
    have hm := mul_le_mul_of_nonneg_right hroom' hr.le
    nlinarith
  have hxS : dist x p≤S*r := by
    apply hx.trans (mul_le_mul_of_nonneg_right _ hr.le)
    nlinarith [mul_nonneg ht.le M.coe_nonneg]
  refine ⟨hyS,?_,?_⟩
  · have hm := (abs_le.mp (hv.2.1 x y hxS hyS)).2
    linarith
  · have hs := (abs_le.mp (pointed_square_distance_error hr hε hv hxS hyS hdyr)).2
    have hsq := div_le_div_of_nonneg_right hs (show 0≤2*t by positivity)
    rw [sub_div] at hsq
    have hvalue := (abs_le.mp (he y hyS)).1
    have hupper := pointed_hopfLax_upper hr ht hε hρ hroom hv hF hψ he hx
    rw [hy,scaled_quadratic_cost ht hr] at hupper
    dsimp only [pointedHopfError]
    ring_nf at hsq hupper ⊢
    linarith

end RegularPointCoordinates

end

end OAI
