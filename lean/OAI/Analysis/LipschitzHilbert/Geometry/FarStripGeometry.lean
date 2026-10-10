import OAI.Analysis.LipschitzHilbert.Estimates.PopularGroups

namespace OAI

/-! Quantitative transverse coordinates and the actual area bound for
intersections of two thin rectangles. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert.Rectangle

theorem norm_le_coordinate_sum (R : Rectangle) (z : Plane) :
    ‖z‖ ≤ |R.axes.repr z 0|+|R.axes.repr z 1| := by
  calc
    ‖z‖ = ‖∑ i : Fin 2, R.axes.repr z i • R.axes i‖ := by rw [R.axes.sum_repr]
    _ ≤ ∑ i : Fin 2, ‖R.axes.repr z i • R.axes i‖ := norm_sum_le _ _
    _ = _ := by simp only [Fin.sum_univ_two,norm_smul,R.axes.norm_eq_one,mul_one,Real.norm_eq_abs]

theorem transverse_coordinate_comparable (R S : Rectangle)
    (hangle : dist (R.axes 0) (S.axes 0) ≤ 1) :
    dist (R.axes 0) (S.axes 0)/2 ≤ |R.axes.repr (S.axes 0) 1| ∧
      |R.axes.repr (S.axes 0) 1| ≤ dist (R.axes 0) (S.axes 0) := by
  let a := R.axes.repr (S.axes 0) 0
  let b := R.axes.repr (S.axes 0) 1
  have hunit := R.axes.sum_sq_inner_right (S.axes 0)
  simp only [Fin.sum_univ_two,←R.axes.repr_apply_apply,S.axes.norm_eq_one,one_pow] at hunit
  change a^2+b^2=1 at hunit
  have ha : |a| ≤ 1 := by
    exact (R.abs_coordinate_le_norm (S.axes 0) 0).trans_eq (S.axes.norm_eq_one 0)
  have hd := R.abs_coordinate_le_norm (S.axes 0-R.axes 0) 0
  have hb := R.abs_coordinate_le_norm (S.axes 0-R.axes 0) 1
  have ht := R.norm_le_coordinate_sum (S.axes 0-R.axes 0)
  simp only [map_sub,PiLp.sub_apply] at hd hb ht
  have h00 : R.axes.repr (R.axes 0) 0 = 1 := by simp
  have h01 : R.axes.repr (R.axes 0) 1 = 0 := by simp
  rw [h00] at hd ht
  rw [h01] at hb ht
  change |a-1| ≤ ‖S.axes 0-R.axes 0‖ at hd
  change |b-0| ≤ ‖S.axes 0-R.axes 0‖ at hb
  change ‖S.axes 0-R.axes 0‖ ≤ |a-1|+|b-0| at ht
  have hn : ‖S.axes 0-R.axes 0‖ = dist (R.axes 0) (S.axes 0) := by rw [dist_comm,dist_eq_norm]
  rw [hn] at hd hb ht
  have ha0 : 0 ≤ a := by linarith [(abs_le.mp hd).1]
  have ha1 : a ≤ 1 := (abs_le.mp ha).2
  have hsquare : (1-a)^2 ≤ |b|^2 := by rw [sq_abs]; nlinarith
  have hcomp : 1-a ≤ |b| :=
    (sq_le_sq₀ (by linarith : 0 ≤ 1-a) (abs_nonneg b)).mp hsquare
  have habs : |a-1| = 1-a := by rw [abs_of_nonpos (by linarith)]; ring
  rw [habs,sub_zero] at ht
  exact ⟨by linarith,by simpa only [sub_zero] using hb⟩

end LipschitzHilbert.Rectangle

namespace LipschitzHilbert

theorem strip_projection_area_swap (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (P : Set ℝ) (hP : MeasurableSet P) (a b c w : ℝ) (ha : a ≠ 0) (hw : 0 ≤ w)
    (hproj : ∀ z ∈ E, z.2 ∈ P) (hstrip : ∀ z ∈ E, |a*z.1+b*z.2-c| ≤ w) :
    (volume.prod volume) E ≤ ENNReal.ofReal (2*w/|a|)*volume P := by
  have h := strip_projection_area (Prod.swap ⁻¹' E) (hE.preimage measurable_swap)
    P hP b a c w ha hw (fun z hz => hproj z.swap hz)
    (fun z hz => by simpa only [Prod.fst_swap,Prod.snd_swap,add_comm] using hstrip z.swap hz)
  have he : (volume.prod volume) (Prod.swap ⁻¹' E) = (volume.prod volume) E :=
    (MeasureTheory.Measure.measurePreserving_swap (μ := volume) (ν := volume)).measure_preimage hE.nullMeasurableSet
  rwa [he] at h

namespace Rectangle

theorem intersection_area_transverse (R S : Rectangle)
    (ha : R.axes.repr (S.axes 0) 1 ≠ 0) :
    volume (R.carrier ∩ S.carrier) ≤
      ENNReal.ofReal (R.short / |R.axes.repr (S.axes 0) 1|)*ENNReal.ofReal S.short := by
  let E := S.orthogonalCoordinates '' (R.carrier ∩ S.carrier)
  have hE : IsCompact E := (R.isCompact_carrier.inter_right S.isClosed_carrier).image
    S.continuous_orthogonalCoordinates
  have h := strip_projection_area_swap E hE.measurableSet
    (Icc (-S.short/2) (S.short/2)) measurableSet_Icc
    (R.axes.repr (S.axes 0) 1) (R.axes.repr (S.axes 1) 1)
    (-R.axes.repr (S.center-R.center) 1) (R.short/2) ha (half_pos R.short_pos).le
    (fun z hz => by
      obtain ⟨x,hx,rfl⟩ := hz
      simpa only [mem_Icc,neg_div,orthogonalCoordinates_apply] using abs_le.mp hx.2.2)
    (fun z hz => by
      obtain ⟨x,hx,rfl⟩ := hz
      have hh := hx.1.2
      rw [change_transverse_coordinates R S x] at hh
      simpa only [sub_neg_eq_add] using hh)
  have he : (volume.prod volume) E = volume (R.carrier ∩ S.carrier) := by
    have he := S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv E
    rw [Set.preimage_image_eq _ S.orthogonalCoordinates.injective] at he
    exact he.symm
  rw [he,Real.volume_Icc,show S.short/2- -S.short/2=S.short by ring,
    show 2*(R.short/2)=R.short by ring] at h
  exact h

theorem intersection_area_angle (R S : Rectangle)
    (hpos : 0 < dist (R.axes 0) (S.axes 0))
    (hangle : dist (R.axes 0) (S.axes 0) ≤ 1) :
    volume (R.carrier ∩ S.carrier) ≤
      ENNReal.ofReal (2*R.short / dist (R.axes 0) (S.axes 0))*ENNReal.ofReal S.short := by
  have hc := R.transverse_coordinate_comparable S hangle
  have hp : 0 < |R.axes.repr (S.axes 0) 1| := lt_of_lt_of_le (half_pos hpos) hc.1
  have hn : R.axes.repr (S.axes 0) 1 ≠ 0 := abs_pos.mp hp
  refine (R.intersection_area_transverse S hn).trans (mul_le_mul' ?_ le_rfl)
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ hp hpos).mpr
  have hh := mul_le_mul_of_nonneg_left hc.1 R.short_pos.le
  nlinarith

end Rectangle
end LipschitzHilbert

end

end OAI
