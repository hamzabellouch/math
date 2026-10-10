import OAI.Analysis.LipschitzHilbert.Geometry.NearRectangleSection

namespace OAI

/-! Projection of a transverse rectangle section onto an actual line.
The dilation is explicit, and no geometric covering hypothesis is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

def projectionTime (S : Rectangle) (x w : Plane) (u : ℝ) : ℝ :=
  (u-(S.orthogonalCoordinates x).2) / S.axes.repr w 1

theorem line_coordinate (S : Rectangle) (x w : Plane) (t : ℝ) (i : Fin 2) :
    S.axes.repr (x+t • w-S.center) i =
      S.axes.repr (x-S.center) i+t*S.axes.repr w i := by
  have he : x+t • w-S.center = (x-S.center)+t • w := by abel
  rw [he,map_add,PiLp.add_apply,map_smul]
  rfl

theorem projectionTime_bound (R S : Rectangle) (x w : Plane) (B : ℝ)
    (hB : 0 ≤ B) (hw : 1/2 ≤ |S.axes.repr w 1|)
    {u : ℝ} (hu : u ∈ nearSection R S x B) :
    |S.projectionTime x w u| ≤ 2*B*R.short := by
  have hd : 0 < |S.axes.repr w 1| := by linarith
  have hh : |u-(S.orthogonalCoordinates x).2| ≤ B*R.short := by
    apply abs_le.mpr
    constructor <;> linarith [hu.2.1,hu.2.2]
  rw [projectionTime,abs_div]
  apply (div_le_iff₀ hd).mpr
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hB R.short_pos.le))
  nlinarith

theorem projected_point_mem_dilate (R S : Rectangle) (x w : Plane)
    (hx : x ∈ R.carrier) (hint : (R.carrier ∩ S.carrier).Nonempty)
    (hL : R.long ≤ S.long) (B : ℝ) (hB : 0 ≤ B) (hw : ‖w‖ ≤ 1)
    (htrans : 1/2 ≤ |S.axes.repr w 1|) {u : ℝ} (hu : u ∈ nearSection R S x B) :
    x+S.projectionTime x w u • w ∈ (S.dilate (4*B+5) (by linarith)).carrier := by
  obtain ⟨y,hyR,hyS⟩ := hint
  have hdist : |S.axes.repr (x-S.center) 0-S.axes.repr (y-S.center) 0| ≤ 2*R.long := by
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (x-y) 0).trans (by simpa only [dist_eq_norm] using R.dist_le_two_long hx hyR)
  have hxl : |S.axes.repr (x-S.center) 0| ≤ 5*S.long/2 := by
    calc
      _ = |(S.axes.repr (x-S.center) 0-S.axes.repr (y-S.center) 0)+S.axes.repr (y-S.center) 0| := by congr 1; ring
      _ ≤ |S.axes.repr (x-S.center) 0-S.axes.repr (y-S.center) 0|+|S.axes.repr (y-S.center) 0| := abs_add_le _ _
      _ ≤ 5*S.long/2 := by linarith [hyS.1]
  have ht := projectionTime_bound R S x w B hB htrans hu
  have hw0 : |S.axes.repr w 0| ≤ 1 := (S.abs_coordinate_le_norm w 0).trans hw
  have hprod : |S.projectionTime x w u * S.axes.repr w 0| ≤ 2*B*R.short := by
    rw [abs_mul]
    have h := mul_le_mul ht hw0 (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB) R.short_pos.le)
    simpa only [mul_one] using h
  constructor
  · change |S.axes.repr (x+S.projectionTime x w u • w-S.center) 0| ≤ (4*B+5)*S.long/2
    rw [line_coordinate]
    have hs := mul_le_mul_of_nonneg_left (R.short_le_long.trans hL) (by linarith : 0 ≤ 2*B)
    exact (abs_add_le _ _).trans (by nlinarith)
  · change |S.axes.repr (x+S.projectionTime x w u • w-S.center) 1| ≤ (4*B+5)*S.short/2
    have hd : S.axes.repr w 1 ≠ 0 := by intro hd; norm_num [hd] at htrans
    rw [line_coordinate,projectionTime,div_mul_cancel₀ _ hd]
    have he : S.axes.repr (x-S.center) 1+(u-(S.orthogonalCoordinates x).2)=u := by
      rw [orthogonalCoordinates_apply]
      ring
    rw [he]
    have huabs : |u| ≤ S.short/2 := abs_le.mpr (by simpa only [mem_Icc,neg_div] using hu.1)
    nlinarith [S.short_pos]

def nearLineParameters (R S : Rectangle) (x w : Plane) (B : ℝ) : Set ℝ :=
  (fun t => (S.orthogonalCoordinates x).2+t*S.axes.repr w 1) ⁻¹' nearSection R S x B

theorem nearSection_measurable (R S : Rectangle) (x : Plane) (B : ℝ) :
    MeasurableSet (nearSection R S x B) := measurableSet_Icc.inter measurableSet_Icc

theorem nearLineParameters_subset (R S : Rectangle) (x w : Plane)
    (hx : x ∈ R.carrier) (hint : (R.carrier ∩ S.carrier).Nonempty)
    (hL : R.long ≤ S.long) (B : ℝ) (hB : 0 ≤ B) (hw : ‖w‖ ≤ 1)
    (htrans : 1/2 ≤ |S.axes.repr w 1|) :
    nearLineParameters R S x w B ⊆ Icc (-2*B*R.short) (2*B*R.short) ∩
      {t | x+t • w ∈ (S.dilate (4*B+5) (by linarith)).carrier} := by
  intro t ht
  have hu : (S.orthogonalCoordinates x).2+t*S.axes.repr w 1 ∈ nearSection R S x B := ht
  have hd : S.axes.repr w 1 ≠ 0 := by intro hd; norm_num [hd] at htrans
  have he : S.projectionTime x w ((S.orthogonalCoordinates x).2+t*S.axes.repr w 1)=t := by
    unfold projectionTime
    field_simp [hd]
    ring
  have hb := projectionTime_bound R S x w B hB htrans hu
  have hm := projected_point_mem_dilate R S x w hx hint hL B hB hw htrans hu
  rw [he] at hb hm
  exact ⟨by simpa only [mem_Icc,neg_mul] using abs_le.mp hb,hm⟩

theorem nearSection_le_lineParameters (R S : Rectangle) (x w : Plane) (B : ℝ)
    (hw : ‖w‖ ≤ 1) (htrans : 1/2 ≤ |S.axes.repr w 1|) :
    volume (nearSection R S x B) ≤ volume (nearLineParameters R S x w B) := by
  have hd : S.axes.repr w 1 ≠ 0 := by intro hd; norm_num [hd] at htrans
  have he : nearLineParameters R S x w B =
      (fun t : ℝ => t*S.axes.repr w 1) ⁻¹'
      ((fun u : ℝ => (S.orthogonalCoordinates x).2+u) ⁻¹' nearSection R S x B) := rfl
  rw [he,Real.volume_preimage_mul_right hd,
    (measurePreserving_add_left volume (S.orthogonalCoordinates x).2).measure_preimage
      (nearSection_measurable R S x B).nullMeasurableSet]
  have hcoord : |S.axes.repr w 1| ≤ 1 := (S.abs_coordinate_le_norm w 1).trans hw
  have hi : (1:ℝ) ≤ |(S.axes.repr w 1)⁻¹| := by
    rw [abs_inv]
    exact (one_le_inv₀ (abs_pos.mpr hd)).mpr hcoord
  calc
    _ = 1 * volume (nearSection R S x B) := (one_mul _).symm
    _ ≤ _ := mul_le_mul' (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hi) le_rfl

theorem nearSection_le_line_integral (R S : Rectangle) (x w : Plane)
    (hx : x ∈ R.carrier) (hint : (R.carrier ∩ S.carrier).Nonempty)
    (hL : R.long ≤ S.long) (B : ℝ) (hB : 0 ≤ B) (hw : ‖w‖ ≤ 1)
    (htrans : 1/2 ≤ |S.axes.repr w 1|) :
    volume (nearSection R S x B) ≤
      ∫⁻ t in Icc (-2*B*R.short) (2*B*R.short),
        (S.dilate (4*B+5) (by linarith)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (x+t • w) := by
  have hline : MeasurableSet {t : ℝ | x+t • w ∈ (S.dilate (4*B+5) (by linarith)).carrier} :=
    (S.dilate (4*B+5) (by linarith)).measurableSet_carrier.preimage (by fun_prop)
  have he : (fun t : ℝ => (S.dilate (4*B+5) (by linarith)).carrier.indicator
      (fun _ => (1:ℝ≥0∞)) (x+t • w)) =
      {t : ℝ | x+t • w ∈ (S.dilate (4*B+5) (by linarith)).carrier}.indicator (fun _ => (1:ℝ≥0∞)) := by
    funext t
    by_cases ht : x+t • w ∈ (S.dilate (4*B+5) (by linarith)).carrier <;> simp [ht]
  rw [he,lintegral_indicator hline,lintegral_const,Measure.restrict_restrict hline,
    Measure.restrict_apply_univ,one_mul]
  exact (nearSection_le_lineParameters R S x w B hw htrans).trans
    (measure_mono (by simpa only [inter_comm] using nearLineParameters_subset R S x w hx hint hL B hB hw htrans))

end LipschitzHilbert.Rectangle

end

end OAI
