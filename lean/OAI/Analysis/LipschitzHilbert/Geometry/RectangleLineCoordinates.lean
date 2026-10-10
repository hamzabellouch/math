import OAI.Analysis.LipschitzHilbert.Geometry.NearRectangleLine
import OAI.Analysis.LipschitzHilbert.Estimates.PositiveAuxiliaryAverages

namespace OAI

/-! Exact parameter changes for the line averages in the near-angle
rectangle estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

theorem orthogonalCoordinates_symm_line (D : Rectangle) (x : Plane) (t : ℝ) :
    D.orthogonalCoordinates.symm ((D.orthogonalCoordinates x).1+t,(D.orthogonalCoordinates x).2) =
      x+t • D.axes 0 := by
  apply D.orthogonalCoordinates.injective
  rw [D.orthogonalCoordinates.apply_symm_apply]
  apply Prod.ext
  · change D.axes.repr (x-D.center) 0+t = D.axes.repr (x+t • D.axes 0-D.center) 0
    rw [line_coordinate]
    simp
  · change D.axes.repr (x-D.center) 1 = D.axes.repr (x+t • D.axes 0-D.center) 1
    rw [line_coordinate]
    simp

theorem line_integral_change_origin (D : Rectangle) {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (x : Plane) (r : ℝ) :
    (∫⁻ t in Icc (-r) r, f (x+t • D.axes 0)) =
      ∫⁻ u in Icc ((D.orthogonalCoordinates x).1-r) ((D.orthogonalCoordinates x).1+r),
        f (D.orthogonalCoordinates.symm (u,(D.orthogonalCoordinates x).2)) := by
  let c := (D.orthogonalCoordinates x).1
  let b := (D.orthogonalCoordinates x).2
  have hF : Measurable (fun u : ℝ => f (D.orthogonalCoordinates.symm (u,b))) :=
    (hf.comp D.orthogonalCoordinates.symm.measurable).comp (measurable_id.prodMk measurable_const)
  have he : (fun t : ℝ => c+t) ⁻¹' Icc (c-r) (c+r) = Icc (-r) r := by
    ext t
    simp only [mem_preimage,mem_Icc]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hh := (measurePreserving_add_left volume c).setLIntegral_comp_preimage (s := Icc (c-r) (c+r)) measurableSet_Icc hF
  rw [he] at hh
  calc
    _ = ∫⁻ t in Icc (-r) r, f (D.orthogonalCoordinates.symm (c+t,b)) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall (fun t => congrArg f (D.orthogonalCoordinates_symm_line x t).symm)
    _ = _ := hh

theorem near_intersection_line_integral (R S D : Rectangle) (x : Plane)
    (hx : x ∈ R.carrier) (hint : (R.carrier ∩ S.carrier).Nonempty) (hL : R.long ≤ S.long)
    (A : ℝ) (hA : 0 ≤ A)
    (hangle : R.long * dist (S.axes 0) (R.axes 0) ≤ A * R.short)
    (htrans : 1/2 ≤ |S.axes.repr (D.axes 0) 1|) :
    volume (R.carrier ∩ S.carrier) ≤ ENNReal.ofReal (4*R.long) *
      ∫⁻ u in Icc ((D.orthogonalCoordinates x).1-2*(A+1)*R.short)
          ((D.orthogonalCoordinates x).1+2*(A+1)*R.short),
        (S.dilate (4*(A+1)+5) (by linarith)).carrier.indicator (fun _ => (1:ℝ≥0∞))
          (D.orthogonalCoordinates.symm (u,(D.orthogonalCoordinates x).2)) := by
  have hb : 0 ≤ A+1 := by linarith
  have hw : ‖D.axes 0‖ ≤ 1 := by rw [D.axes.norm_eq_one]
  have h := (near_intersection_area R S x hx A hangle).trans
    (mul_le_mul' le_rfl (nearSection_le_line_integral R S x (D.axes 0) hx hint hL (A+1) hb hw htrans))
  have he := line_integral_change_origin D
    (f := (S.dilate (4*(A+1)+5) (by linarith)).carrier.indicator (fun _ => (1:ℝ≥0∞)))
    (measurable_const.indicator (S.dilate (4*(A+1)+5) (by linarith)).measurableSet_carrier)
    x (2*(A+1)*R.short)
  simp only [neg_mul] at h
  rw [he] at h
  exact h

end LipschitzHilbert.Rectangle

end

end OAI
