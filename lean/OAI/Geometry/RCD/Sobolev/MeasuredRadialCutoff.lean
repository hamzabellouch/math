import OAI.Geometry.RCD.Sobolev.NestedBallCutoff
import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # Physical radial cutoffs and their prescribed Euclidean limits -/

open Set Filter MeasureTheory Metric
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def euclideanNestedCutoff (n : ℕ) {a b : ℝ} (hab : a<b) : Euclidean n →ᵇ ℝ := by
  refine ⟨⟨nestedBallCutoff 0 a b,(nestedBallCutoff_lipschitz 0 hab).continuous⟩,2,?_⟩
  intro x y
  have hx := nestedBallCutoff_bounds (0:Euclidean n) a b x
  have hy := nestedBallCutoff_bounds (0:Euclidean n) a b y
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith

theorem measured_radial_cutoff_error {n : ℕ} {p : X} {r S ε a b : ℝ}
    (hr : 0<r) (hS : 0≤S) (hab : a<b) {v : X → Euclidean n}
    (hv : IsPointedApproximation p 0 r S ε v) {x : X} (hx : dist x p≤S*r) :
    |nestedBallCutoff p (a*r) (b*r) x-euclideanNestedCutoff n hab (v x)|≤2*ε/(b-a) := by
  have hd := pointed_radial_distance hr hS hv hx
  have harg : (b*r-dist p x)/(b*r-a*r)=(b-dist x p/r)/(b-a) := by
    rw [dist_comm p x]
    field_simp [hr.ne',sub_ne_zero.mpr (ne_of_gt hab)]
  change |clipUnit ((b*r-dist p x)/(b*r-a*r))-clipUnit ((b-dist 0 (v x))/(b-a))|≤_
  rw [harg,dist_zero_left]
  have hclip := clipUnit_lipschitz.dist_le_mul ((b-dist x p/r)/(b-a)) ((b-‖v x‖)/(b-a))
  have he : |(b-dist x p/r)/(b-a)-(b-‖v x‖)/(b-a)|=|‖v x‖-dist x p/r|/(b-a) := by
    rw [← sub_div,show b-dist x p/r-(b-‖v x‖)=‖v x‖-dist x p/r by ring,
      abs_div,abs_of_pos (sub_pos.mpr hab)]
  calc
    _ ≤ |(b-dist x p/r)/(b-a)-(b-‖v x‖)/(b-a)| := by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hclip
    _ = _ := he
    _ ≤ _ := div_le_div_of_nonneg_right hd (sub_pos.mpr hab).le

theorem measured_radial_cutoff_square_error {n : ℕ} {p : X} {r S ε a b : ℝ}
    (hr : 0<r) (hS : 0≤S) (hab : a<b) {v : X → Euclidean n}
    (hv : IsPointedApproximation p 0 r S ε v) {x : X} (hx : dist x p≤S*r) :
    |(nestedBallCutoff p (a*r) (b*r) x)^2-(euclideanNestedCutoff n hab (v x))^2|≤4*ε/(b-a) := by
  have herror := measured_radial_cutoff_error hr hS hab hv hx
  have hleft := nestedBallCutoff_bounds p (a*r) (b*r) x
  have hright := nestedBallCutoff_bounds (0:Euclidean n) a b (v x)
  change 0≤euclideanNestedCutoff n hab (v x) ∧ euclideanNestedCutoff n hab (v x)≤1 at hright
  have he : |(nestedBallCutoff p (a*r) (b*r) x)^2-(euclideanNestedCutoff n hab (v x))^2|≤
      2*|nestedBallCutoff p (a*r) (b*r) x-euclideanNestedCutoff n hab (v x)| := by
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg hleft.1 hright.1)]
    nlinarith [abs_nonneg (nestedBallCutoff p (a*r) (b*r) x-euclideanNestedCutoff n hab (v x))]
  calc
    _ ≤ _ := he
    _ ≤ 2*(2*ε/(b-a)) := mul_le_mul_of_nonneg_left herror (by norm_num)
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
