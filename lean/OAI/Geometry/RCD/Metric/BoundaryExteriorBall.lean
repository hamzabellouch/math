import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # A definite exterior ball at every point of an inner boundary shell -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_boundary_exterior_ball {n : ℕ} {p x : X} {r S R δ ε : ℝ}
    (hr : 0<r) (hδ : 0<δ) (hR : 4*δ≤R) (hS : R+2*δ≤S)
    (_hε : 0≤ε) (hεδ : ε≤δ/8) (V : X → Euclidean n)
    (hV : IsPointedApproximation p 0 r S ε V)
    (hx₀ : (R-δ)*r≤dist x p) (hx₁ : dist x p≤R*r) :
    ∃ y : X, dist y p≤S*r ∧ (R+δ/2)*r≤dist y p ∧ dist x y≤4*δ*r ∧
      ball y (δ/4*r)⊆ball x (5*δ*r) \ ball p (R*r) := by
  have hS0 : 0≤S := by linarith
  have hxS : dist x p≤S*r := hx₁.trans (mul_le_mul_of_nonneg_right (by linarith) hr.le)
  have hd := abs_le.mp (pointed_radial_distance hr hS0 hV hxS)
  have hxlo : R-δ≤dist x p/r := (le_div_iff₀ hr).mpr hx₀
  have hxhi : dist x p/r≤R := (div_le_iff₀ hr).mpr hx₁
  have hnorm : 0<‖V x‖ := by linarith
  have hnormhi : ‖V x‖≤R+δ := by linarith
  let a := (R+δ)/‖V x‖
  have ha : 1≤a := (le_div_iff₀ hnorm).mpr (by simpa only [one_mul] using hnormhi)
  have ha0 : 0<a := zero_lt_one.trans_le ha
  let z := a • V x
  have hz : ‖z‖=R+δ := by
    dsimp only [z]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha0]
    dsimp only [a]
    exact div_mul_cancel₀ _ hnorm.ne'
  have hzx : dist z (V x)=R+δ-‖V x‖ := by
    rw [dist_eq_norm]
    have he : z-V x=(a-1) • V x := by dsimp only [z]; rw [sub_smul,one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ha)]
    dsimp only [a]
    field_simp
  obtain ⟨y,hyS,hyz⟩ := hV.2.2 z (by rw [dist_zero_right,hz]; linarith)
  have hyz' : dist (V y) z≤ε := hyz
  have hnormy := (dist_triangle z (V y) 0)
  rw [dist_comm z (V y),dist_zero_right,dist_zero_right,hz] at hnormy
  have hdy := abs_le.mp (pointed_radial_distance hr hS0 hV hyS)
  have hylo : R+δ/2≤dist y p/r := by linarith
  have hdist := (abs_le.mp (hV.2.1 x y hxS hyS)).1
  have htri := dist_triangle (V x) z (V y)
  rw [dist_comm (V x) z,dist_comm z (V y),hzx] at htri
  have hxy : dist x y/r≤4*δ := by linarith
  refine ⟨y,hyS,(le_div_iff₀ hr).mp hylo,(div_le_iff₀ hr).mp hxy,?_⟩
  intro v hv
  constructor
  · have ht := dist_triangle v y x
    rw [dist_comm y x] at ht
    have hv' : dist v y<δ/4*r := hv
    have hxy' := (div_le_iff₀ hr).mp hxy
    have hδr := mul_pos hδ hr
    change dist v x<5*δ*r
    nlinarith
  · intro hvp
    have ht := dist_triangle y v p
    rw [dist_comm y v] at ht
    have hlow := (le_div_iff₀ hr).mp hylo
    have hδr : 0<δ*r := mul_pos hδ hr
    have hv' : dist v y<δ/4*r := hv
    have hvp' : dist v p<R*r := hvp
    nlinarith

end RegularPointCoordinates

end

end OAI
