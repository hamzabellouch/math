import OAI.Analysis.LipschitzHilbert.Geometry.RectangleDilation

namespace OAI

/-! A transverse section bound for intersecting rectangles. This is the
area-to-line reduction behind the near-angle part of Lacey--Li (3.5). -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

def nearSection (R S : Rectangle) (x : Plane) (B : ℝ) : Set ℝ :=
  Icc (-S.short/2) (S.short/2) ∩
    Icc ((S.orthogonalCoordinates x).2-B*R.short) ((S.orthogonalCoordinates x).2+B*R.short)

theorem coordinate_difference (S : Rectangle) (x y : Plane) (i : Fin 2) :
    S.axes.repr (y-S.center) i-S.axes.repr (x-S.center) i = S.axes.repr (y-x) i := by
  simp only [S.axes.repr_apply_apply,inner_sub_right]
  ring

theorem near_intersection_coordinates (R S : Rectangle) (x : Plane) (hx : x ∈ R.carrier)
    (A : ℝ) (hangle : R.long * dist (S.axes 0) (R.axes 0) ≤ A * R.short) :
    S.orthogonalCoordinates '' (R.carrier ∩ S.carrier) ⊆
      Icc ((S.orthogonalCoordinates x).1-2*R.long) ((S.orthogonalCoordinates x).1+2*R.long) ×ˢ
        nearSection R S x (A+1) := by
  rintro z ⟨y,hy,rfl⟩
  have hlong : |S.axes.repr (y-S.center) 0-S.axes.repr (x-S.center) 0| ≤ 2*R.long := by
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (y-x) 0).trans (by simpa only [dist_eq_norm] using R.dist_le_two_long hy.1 hx)
  have hshort : |S.axes.repr (y-S.center) 1-S.axes.repr (x-S.center) 1| ≤ (A+1)*R.short := by
    rw [coordinate_difference]
    exact (S.transverse_difference_le R hy.1 hx).trans (by nlinarith [R.short_pos])
  simp only [orthogonalCoordinates_apply,nearSection,mem_prod,mem_inter_iff,mem_Icc]
  change (_ ∧ _) ∧ (_ ∧ _)
  constructor
  · obtain ⟨hl,hu⟩ := abs_le.mp hlong
    constructor <;> linarith
  · refine ⟨?_,?_⟩
    · simpa only [neg_div] using abs_le.mp hy.2.2
    · obtain ⟨hl,hu⟩ := abs_le.mp hshort
      constructor <;> linarith

theorem near_intersection_area (R S : Rectangle) (x : Plane) (hx : x ∈ R.carrier)
    (A : ℝ) (hangle : R.long * dist (S.axes 0) (R.axes 0) ≤ A * R.short) :
    volume (R.carrier ∩ S.carrier) ≤
      ENNReal.ofReal (4*R.long) * volume (nearSection R S x (A+1)) := by
  have he : (volume.prod volume) (S.orthogonalCoordinates '' (R.carrier ∩ S.carrier)) =
      volume (R.carrier ∩ S.carrier) := by
    have h := S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv
      (S.orthogonalCoordinates '' (R.carrier ∩ S.carrier))
    rw [Set.preimage_image_eq _ S.orthogonalCoordinates.injective] at h
    exact h.symm
  rw [←he]
  refine (measure_mono (near_intersection_coordinates R S x hx A hangle)).trans_eq ?_
  rw [Measure.prod_prod,Real.volume_Icc]
  congr 2
  ring

end LipschitzHilbert.Rectangle

end

end OAI
