import OAI.Geometry.IsometricImmersion.Caps.FixedMetricLowerCap
import OAI.Geometry.IsometricImmersion.Caps.CapReflectionCalculus

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

def coordinateWordSign : List (Fin 2) → ℝ
  | [] => 1
  | i::ds => (if i=0 then 1 else -1) * coordinateWordSign ds

theorem coordinateWordSign_abs (ds : List (Fin 2)) : |coordinateWordSign ds| = 1 := by
  induction ds with
  | nil => simp [coordinateWordSign]
  | cons i ds ih =>
    rw [coordinateWordSign,abs_mul,ih]
    split_ifs <;> norm_num

theorem orderedPartial_reflectedScalar
    {f : Coord → ℝ} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : reflectPoint p ∈ U) :
    iteratedCoordPartial ds (reflectedScalar f) p =
      coordinateWordSign ds * iteratedCoordPartial ds f (reflectPoint p) := by
  induction ds generalizing p with
  | nil => simp [iteratedCoordPartial,coordinateWordSign,reflectedScalar]
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (reflectedScalar f) =ᶠ[𝓝 p]
        (fun q => coordinateWordSign ds * iteratedCoordPartial ds f (reflectPoint q)) := by
      filter_upwards [(reflectedDomain_isOpen hU).mem_nhds hp] with q hq
      exact ih hq
    have hfd := orderedPartial_contDiffOn hf hU ds
    have hdr : DifferentiableAt ℝ (reflectedScalar (iteratedCoordPartial ds f)) p :=
      ((reflectedScalar_contDiffOn hfd).contDiffAt
        ((reflectedDomain_isOpen hU).mem_nhds hp)).differentiableAt (by simp)
    have hd : DifferentiableAt ℝ (iteratedCoordPartial ds f) (reflectPoint p) :=
      (hfd.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    change coordPartial i (iteratedCoordPartial ds (reflectedScalar f)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    change coordPartial i
      (fun q => coordinateWordSign ds * reflectedScalar (iteratedCoordPartial ds f) q) p = _
    rw [AffineCalculus.coordPartial_const_mul_at hdr,coordPartial_reflectedScalar hd i]
    fin_cases i <;> simp [coordinateWordSign,iteratedCoordPartial]

theorem orderedPartial_reflectedScalar_abs
    {f : Coord → ℝ} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : reflectPoint p ∈ U) :
    |iteratedCoordPartial ds (reflectedScalar f) p| =
      |iteratedCoordPartial ds f (reflectPoint p)| := by
  rw [orderedPartial_reflectedScalar hf hU ds hp,abs_mul,coordinateWordSign_abs,one_mul]

structure UpperCapRectangle (floor : ℝ) where
  left : ℝ
  right : ℝ
  bottom : ℝ
  top : ℝ
  left_gt : -2 < left
  right_lt : right < 2
  top_lt : top < 2
  horizontal : left ≤ right
  vertical : bottom ≤ top
  bottom_gt : floor < bottom
  floor_nonneg : 0 ≤ floor

namespace UpperCapRectangle
variable {floor : ℝ}

def region (r : UpperCapRectangle floor) : Set Coord :=
  closedRectangle r.left r.right r.bottom r.top

def image (r : UpperCapRectangle floor) (Y : ℝ → ℝ → ℝ) : Set Coord :=
  capChart Y '' r.region

def lower (r : UpperCapRectangle floor) : LowerCapRectangle (-floor) where
  left := r.left
  right := r.right
  bottom := -r.top
  top := -r.bottom
  left_gt := r.left_gt
  right_lt := r.right_lt
  bottom_gt := neg_lt_neg r.top_lt
  horizontal := r.horizontal
  vertical := neg_le_neg r.vertical
  top_lt := neg_lt_neg r.bottom_gt
  ceiling_le := neg_nonpos.mpr r.floor_nonneg

theorem region_subset_domain (r : UpperCapRectangle floor) : r.region ⊆ capChartDomain :=
  closedRectangle_subset_capChartDomain r.left_gt r.right_lt
    (by linarith [r.bottom_gt,r.floor_nonneg]) r.top_lt

theorem reflected_region (r : UpperCapRectangle floor) (p : Coord) :
    reflectPoint p ∈ r.lower.region ↔ p ∈ r.region := by
  change (p 0 ∈ Icc r.left r.right ∧ -p 1 ∈ Icc (-r.top) (-r.bottom)) ↔
    (p 0 ∈ Icc r.left r.right ∧ p 1 ∈ Icc r.bottom r.top)
  constructor <;> rintro ⟨ht,hs⟩ <;> refine ⟨ht,?_,?_⟩ <;> linarith [hs.1,hs.2]

theorem conjugate_image (r : UpperCapRectangle floor) (Y : ℝ → ℝ → ℝ) :
    r.image (conjugateFlow Y) = reflectPoint '' r.lower.image Y := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ⟨capChart Y (reflectPoint q),
      ⟨reflectPoint q,(r.reflected_region q).mpr hq,rfl⟩,(conjugateFlow_chart Y q).symm⟩
  · rintro ⟨v,⟨q,hq,rfl⟩,rfl⟩
    refine ⟨reflectPoint q,?_,?_⟩
    · apply (r.reflected_region (reflectPoint q)).mp
      simpa only [reflectPoint_twice] using hq
    · simp only [conjugateFlow_chart,reflectPoint_twice]

theorem image_properties (r : UpperCapRectangle floor) {Y : ℝ → ℝ → ℝ}
    (hchart : ContDiffOn ℝ ∞ (capChart Y) capChartDomain)
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50) :
    IsCompact (r.image Y) ∧ MeasurableSet (r.image Y) ∧ r.image Y ⊆ modelSquare := by
  have hcompact : IsCompact (r.image Y) :=
    (capRectangle_isCompact r.left r.right r.bottom r.top).image_of_continuousOn
      (hchart.continuousOn.mono r.region_subset_domain)
  refine ⟨hcompact,hcompact.measurableSet,?_⟩
  rintro p ⟨q,hq,rfl⟩
  exact modelOpenSquare_subset
    (capChart_mem_modelOpenSquare (r.region_subset_domain hq) (hdisp q (r.region_subset_domain hq)))

theorem coordinateBound_of_reflected
    {z : Coord → ℝ} {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {Y : ℝ → ℝ → ℝ} (r : UpperCapRectangle floor) {n : ℕ} {B : ℝ}
    (hmap : r.image (conjugateFlow Y) ⊆ U)
    (hbound : CoordinateBound (reflectedScalar z) (r.lower.image Y) n B) :
    CoordinateBound z (r.image (conjugateFlow Y)) n B := by
  intro ds hds p hp
  have hp' : p ∈ reflectPoint '' r.lower.image Y := by
    rwa [←r.conjugate_image Y]
  obtain ⟨q,hq,hqp⟩ := hp'
  have he := orderedPartial_reflectedScalar_abs hz hU ds
    (show reflectPoint q ∈ U from hqp.symm ▸ hmap hp)
  rw [hqp] at he
  exact he ▸ hbound ds hds q hq

theorem coordinateL2Bound_of_pointwise
    {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ} (r : UpperCapRectangle floor)
    (hchart : ContDiffOn ℝ ∞ (capChart Y) capChartDomain)
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50)
    {n : ℕ} {B : ℝ} (hB : 0 ≤ B) (hbound : CoordinateBound z (r.image Y) n B) :
    CoordinateL2Bound z (r.image Y) n (originalC8L2Budget B) := by
  obtain ⟨_,hV,hVS⟩ := r.image_properties hchart hdisp
  intro ds hds
  rw [originalC8L2Budget_coe]
  exact (bounded_real_eLpNorm_two hV hB (fun p hp => by
    rw [Real.norm_eq_abs]
    exact hbound ds hds p hp)).trans
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (z := 1/(2 : ℝ))
        (measure_mono hVS) (by norm_num)))

end UpperCapRectangle
end SmoothLocal.Flow.Reflection

end

end OAI
