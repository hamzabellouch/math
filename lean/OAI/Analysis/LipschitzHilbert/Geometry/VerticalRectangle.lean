import OAI.Analysis.LipschitzHilbert.Geometry.SlopeRectangle
import OAI.Analysis.LipschitzHilbert.Geometry.SlopeDirection

namespace OAI

/-! Vertical Euclidean enclosures of fat slope parallelograms. The
constant vertical field makes every such enclosure Lacey--Li admissible. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert

def verticalAxes : OrthonormalBasis (Fin 2) ℝ Plane :=
  (slopeAxes 0).reindex (Equiv.swap 0 1)

theorem verticalAxes_repr_zero (z : Plane) : verticalAxes.repr z 0 = z 1 := by
  rw [OrthonormalBasis.repr_apply_apply, verticalAxes, OrthonormalBasis.reindex_apply]
  simp [slopeAxes_apply, slopeAxisVectors, PiLp.inner_apply, Fin.sum_univ_two]

theorem verticalAxes_repr_one (z : Plane) : verticalAxes.repr z 1 = z 0 := by
  rw [OrthonormalBasis.repr_apply_apply, verticalAxes, OrthonormalBasis.reindex_apply]
  simp [slopeAxes_apply, slopeAxisVectors, PiLp.inner_apply, Fin.sum_univ_two]

def verticalRectangle (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) : Rectangle where
  center := planeCoordinates c
  axes := verticalAxes
  long := b+|s| * a
  short := a
  short_pos := ha
  short_le_long := hab.trans (le_add_of_nonneg_right (by positivity))

theorem mem_verticalRectangle (c z : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hx : |z.1-c.1| ≤ a/2) (hy : |(z.2-c.2)-s*(z.1-c.1)| ≤ b/2) :
    planeCoordinates z ∈ (verticalRectangle c s a b ha hab).carrier := by
  change |verticalAxes.repr (planeCoordinates z-planeCoordinates c) 0| ≤ _ ∧
    |verticalAxes.repr (planeCoordinates z-planeCoordinates c) 1| ≤ _
  rw [verticalAxes_repr_zero,verticalAxes_repr_one]
  refine ⟨?_,hx⟩
  change |z.2-c.2| ≤ (b+|s| * a)/2
  calc
    _ = |((z.2-c.2)-s*(z.1-c.1))+s*(z.1-c.1)| := by congr 1; ring
    _ ≤ |(z.2-c.2)-s*(z.1-c.1)|+|s*(z.1-c.1)| := abs_add_le _ _
    _ ≤ b/2+|s| * (a/2) := add_le_add hy (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg s))
    _ = _ := by ring

theorem volume_verticalRectangle_le (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hs : |s| ≤ 1) :
    volume (verticalRectangle c s a b ha hab).carrier ≤ ENNReal.ofReal (2*a*b) := by
  rw [Rectangle.volume_carrier, ← ENNReal.ofReal_mul (by
    change 0 ≤ b+|s| * a; have hb := ha.trans_le hab; positivity)]
  apply ENNReal.ofReal_le_ofReal
  change (b+|s| * a)*a ≤ _
  have h1 := mul_le_mul_of_nonneg_right hs ha.le
  have h2 := mul_le_mul_of_nonneg_right hab ha.le
  have h3 := mul_le_mul_of_nonneg_right h1 ha.le
  nlinarith

theorem constant_axis_popular (R : Rectangle) :
    R.popularSet (fun _ => R.axes 0) = R.carrier := by
  ext z
  simp only [Rectangle.popularSet, mem_ofPred_eq]
  rw [real_inner_self_eq_norm_sq, R.axes.norm_eq_one, one_pow]
  exact and_iff_left (Real.cos_le_one _)

theorem constant_axis_admissible (R : Rectangle) (δ : ℝ≥0) (hδ : δ ≤ 1) :
    R.Admissible (fun _ => R.axes 0) 0 δ := by
  constructor
  · simp
  · rw [constant_axis_popular]
    exact mul_le_of_le_one_left' (by exact_mod_cast hδ)

theorem verticalRectangle_admissible (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    (verticalRectangle c s a b ha hab).Admissible (fun _ => verticalAxes 0) 0 (1/2) :=
  constant_axis_admissible _ _ (by norm_num)

end LipschitzHilbert

end

end OAI
