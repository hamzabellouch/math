import OAI.Analysis.LipschitzHilbert.Geometry.NearSelectionBound
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! A fixed finite family of transverse directions. Compactness supplies
a universal net, independent of the rectangles later selected. -/
noncomputable section
open Set MeasureTheory Metric
namespace LipschitzHilbert.Rectangle

def transverseFrame (R : Rectangle) : Rectangle where
  center := 0
  axes := R.axes.reindex (Equiv.swap 0 1)
  long := 1
  short := 1
  short_pos := zero_lt_one
  short_le_long := le_rfl

theorem transverseFrame_axis (R : Rectangle) : (transverseFrame R).axes 0 = R.axes 1 := by
  simp [transverseFrame]

theorem exists_finite_transverse_directions :
    ∃ n : ℕ, ∃ D : Fin n → Rectangle, ∀ R : Rectangle,
      ∃ i : Fin n, dist ((D i).axes 0) (R.axes 1) < 1/4 := by
  classical
  let S : Set Plane := Set.range (fun R : Rectangle => R.axes 0)
  have hS : S ⊆ sphere (0:Plane) 1 := by
    rintro w ⟨R,rfl⟩
    simpa only [mem_sphere,dist_zero_right] using R.axes.norm_eq_one 0
  have hcomp : IsCompact (closure S) :=
    (isCompact_sphere (0:Plane) 1).of_isClosed_subset isClosed_closure (closure_minimal hS isClosed_sphere)
  obtain ⟨C,hCS,hCf,hcover⟩ := exists_finite_cover_balls_of_isCompact_closure hcomp (by norm_num : (0:ℝ) < 1/4)
  let : Fintype C := hCf.fintype
  have hc (y : C) : ∃ R : Rectangle, R.axes 0 = y.val := hCS y.property
  choose D hD using hc
  let e := Fintype.equivFin C
  refine ⟨Fintype.card C,fun i => D (e.symm i),?_⟩
  intro R
  have hr : R.axes 1 ∈ S := ⟨R.transverseFrame,R.transverseFrame_axis⟩
  obtain ⟨w,hwC,hw⟩ := mem_iUnion₂.mp (hcover hr)
  let j : C := ⟨w,hwC⟩
  refine ⟨e j,?_⟩
  simpa only [Equiv.symm_apply_apply,hD,mem_ball,dist_comm] using hw

theorem transverse_coordinate_large (S : Rectangle) (w : Plane) (hw : ‖w‖ = 1)
    (hsmall : |S.axes.repr w 0| ≤ 1/2) : 1/2 ≤ |S.axes.repr w 1| := by
  have he := S.axes.sum_sq_inner_right w
  simp only [Fin.sum_univ_two,←S.axes.repr_apply_apply,hw,one_pow] at he
  have h0 : (S.axes.repr w 0)^2 ≤ (1/2:ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (S.axes.repr w 0)) (by norm_num : (0:ℝ) ≤ 1/2)).mpr hsmall
  by_contra hn
  have h1 : (S.axes.repr w 1)^2 < (1/2:ℝ)^2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (S.axes.repr w 1)) (by norm_num : (0:ℝ) ≤ 1/2)).mpr (lt_of_not_ge hn)
  nlinarith

theorem nearby_transverse_coordinate (R S D : Rectangle)
    (hangle : dist (S.axes 0) (R.axes 0) ≤ 1/4)
    (hdir : dist (D.axes 0) (R.axes 1) ≤ 1/4) :
    1/2 ≤ |S.axes.repr (D.axes 0) 1| := by
  apply S.transverse_coordinate_large (D.axes 0) (D.axes.norm_eq_one 0)
  have hD : |R.axes.repr (D.axes 0) 0| ≤ dist (D.axes 0) (R.axes 1) := by
    have hz : R.axes.repr (R.axes 1) 0 = 0 := by simp
    have h := R.abs_coordinate_le_norm (D.axes 0-R.axes 1) 0
    rw [map_sub,PiLp.sub_apply,hz,sub_zero] at h
    simpa only [dist_eq_norm] using h
  have hi : |inner ℝ (S.axes 0) (D.axes 0)-inner ℝ (R.axes 0) (D.axes 0)| ≤ dist (S.axes 0) (R.axes 0) := by
    rw [←inner_sub_left]
    simpa only [D.axes.norm_eq_one,mul_one,dist_eq_norm] using abs_real_inner_le_norm (S.axes 0-R.axes 0) (D.axes 0)
  have htri := abs_add_le
    (inner ℝ (S.axes 0) (D.axes 0)-inner ℝ (R.axes 0) (D.axes 0))
    (inner ℝ (R.axes 0) (D.axes 0))
  simp only [sub_add_cancel] at htri
  rw [S.axes.repr_apply_apply]
  rw [R.axes.repr_apply_apply] at hD
  linarith

end LipschitzHilbert.Rectangle

end

end OAI
