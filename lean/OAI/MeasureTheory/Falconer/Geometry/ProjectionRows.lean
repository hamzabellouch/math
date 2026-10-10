import OAI.MeasureTheory.Falconer.Geometry.TwoPointTubeGeometry
import OAI.MeasureTheory.Falconer.Estimates.TubeSecondMoment
import OAI.MeasureTheory.Falconer.Estimates.Packing

namespace OAI

/-! The row geometry in Orponen--Shmerkin, Appendix A.7, expressed in the
original line chart. A line is incident to only a bounded number of points
on a separated row. Its parameter projection stays close to that row point. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

noncomputable def lineParameterProjection (y : ℝ) (l : Space 2) : ℝ := y*l 0+l 1
noncomputable def rowPoint (y x : ℝ) : Space 2 := WithLp.toLp 2 ![y,x]

@[simp] theorem rowPoint_zero (y x : ℝ) : rowPoint y x 0 = y := rfl
@[simp] theorem rowPoint_one (y x : ℝ) : rowPoint y x 1 = x := rfl

theorem rowPoint_dist (y x z : ℝ) : dist (rowPoint y x) (rowPoint y z) = |x-z| := by
  have he := EuclideanSpace.dist_sq_eq (rowPoint y x) (rowPoint y z)
  simp only [Fin.sum_univ_two,rowPoint_zero,rowPoint_one,Real.dist_eq,sq_abs] at he
  nlinarith [dist_nonneg (x := rowPoint y x) (y := rowPoint y z),abs_nonneg (x-z),sq_abs (x-z)]

theorem lineParameterProjection_dist {y : ℝ} (hy : |y| ≤ 1) (l m : Space 2) :
    |lineParameterProjection y l-lineParameterProjection y m| ≤ 2*dist l m := by
  have h0 : |l 0-m 0| ≤ dist l m := by
    simpa only [dist_eq_norm,Real.norm_eq_abs,PiLp.sub_apply] using (PiLp.norm_apply_le (l-m) 0)
  have h1 : |l 1-m 1| ≤ dist l m := by
    simpa only [dist_eq_norm,Real.norm_eq_abs,PiLp.sub_apply] using (PiLp.norm_apply_le (l-m) 1)
  calc
    _ = |y*(l 0-m 0)+(l 1-m 1)| := by unfold lineParameterProjection; congr 1; ring
    _ ≤ |y| * |l 0-m 0|+|l 1-m 1| := by simpa only [abs_mul] using abs_add_le (y*(l 0-m 0)) (l 1-m 1)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hy (abs_nonneg (l 0-m 0))]

theorem tube_projection_near {δ : ℝ} (hδ : 0 ≤ δ) {x l : Space 2}
    (hl : |l 0| ≤ 1) (hi : TubeIncident δ x l) :
    |x 1-lineParameterProjection (x 0) l| ≤ 2*δ := by
  simpa only [lineParameterProjection,mul_comm,sub_add_eq_sub_sub] using tube_residual_le hδ hl hi

theorem row_dist_projection {x : Space 2} {y : ℝ} (hy : x 0 = y) (v : ℝ) :
    dist x (rowPoint y v) = |x 1-v| := by
  have hx : x = rowPoint y (x 1) := by
    ext i
    fin_cases i
    · exact hy
    · rfl
  rw [hx,rowPoint_dist]
  rfl

theorem separated_row_tube_count {δ y : ℝ} (hδ : 0 < δ)
    {P : Finset (Space 2)} (hP : FiniteSeparatedAt δ P)
    (hrow : ∀ x ∈ P, x 0 = y) {l : Space 2} (hl : |l 0| ≤ 1) :
    ((P.filter fun x => TubeIncident δ x l).card : ℝ) ≤ 25 := by
  classical
  have hb := separated_ball_card (P.filter fun x => TubeIncident δ x l)
    (rowPoint y (lineParameterProjection y l)) hδ (r := 2*δ) (by positivity)
    (fun x hx z hz hne => hP x (Finset.mem_filter.mp hx).1 z (Finset.mem_filter.mp hz).1 hne)
    (fun x hx => ?_)
  · have he : 2*(2*δ)/δ+1 = (5 : ℝ) := by field_simp; ring
    norm_num only [he] at hb
    exact hb
  · obtain ⟨hxP,hxi⟩ := Finset.mem_filter.mp hx
    rw [row_dist_projection (hrow x hxP)]
    have hh := tube_projection_near hδ.le hl hxi
    rwa [hrow x hxP] at hh

theorem row_tube_union_count {δ y : ℝ} (hδ : 0 < δ)
    {P : Finset (Space 2)} (hP : FiniteSeparatedAt δ P)
    (hrow : ∀ x ∈ P, x 0 = y) (T : Space 2 → Finset (Space 2))
    (hchart : ∀ x ∈ P, InBoundedLineChart (T x))
    (hinc : ∀ x ∈ P, ∀ l ∈ T x, TubeIncident δ x l) :
    (∑ x ∈ P, ((T x).card : ℝ)) ≤ 25*((P.biUnion T).card : ℝ) := by
  classical
  rw [← sum_tubeDegree]
  calc
    _ ≤ ∑ _l ∈ P.biUnion T, (25 : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      obtain ⟨x,hx,hxl⟩ := Finset.mem_biUnion.mp hl
      have hls := (hchart x hx l hxl).1
      have hsub : P.filter (fun x => l ∈ T x) ⊆ P.filter (fun x => TubeIncident δ x l) := by
        intro z hz
        obtain ⟨hz,hzl⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hz,hinc z hz l hzl⟩
      have he : tubeDegree P T l = ((P.filter fun x => l ∈ T x).card : ℝ) := by
        unfold tubeDegree
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
      rw [he]
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (separated_row_tube_count hδ hP hrow hls)
    _ = _ := by simp; ring

end Falconer

end OAI
