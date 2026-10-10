import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfInfiniteField
import OAI.Analysis.CoulombIonization.FieldAnalysis.LaplacianCompDilation

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian

lemma tfInfiniteField_dominates_dilation {a : ℝ} (ha : 1 ≤ a) (x : TFSpace) (hx : x ≠ 0) :
    CoulombPDE.shiftedDilation a (tfIncreasingData 0).field x ≤ tfInfiniteField x := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  obtain ⟨n, hn⟩ := exists_nat_gt (a^3)
  have hw : a^3 * ((0:ℝ)+1) < (n:ℝ)+1 := by nlinarith
  have hF := (tfIncreasingData 0).finiteProfile (by positivity)
  have hh := CoulombPDE.compare_subsolution_finite tfReactionCoefficient_pos.le (by positivity) hw
    ((tfIncreasingData n).finiteProfile (by positivity))
    (hF.shifted_dilation_regular ha0)
    (fun y hy => (hF.shifted_dilation_equation ha0 y hy).ge)
    (by simpa only [Nat.cast_zero] using hF.shifted_dilation_near ha0) (hF.shifted_dilation_far ha) x hx
  apply hh.trans
  rw [← (tfIncreasingData n).radialField_eq (by positivity) hx]
  exact tfIncreasingField_le (norm_pos_iff.mpr hx) n

lemma tf_first_field_large : ∃ (r₀ : ℝ), 0 < r₀ ∧ 2 ≤ (tfIncreasingData 0).field (r₀ • radialAxis) := by
  obtain ⟨C, hC, a, ha, hn⟩ := ((tfIncreasingData 0).finiteProfile (by positivity)).nucleus
  let r₀ := min a (1/(C+2))
  have hr : 0 < r₀ := lt_min ha (div_pos zero_lt_one (by linarith))
  refine ⟨r₀, hr, ?_⟩
  have hh := (abs_le.mp (hn (r₀ • radialAxis) (TFUnitData.ray_ne_zero hr)
    (by rw [TFUnitData.ray_norm hr]; exact min_le_left _ _))).1
  rw [TFUnitData.ray_norm hr] at hh
  have ht := (le_div_iff₀ (show 0 < C+2 by linarith)).mp (show r₀ ≤ 1/(C+2) from min_le_right _ _)
  have hi : C+2 ≤ 1/r₀ := (le_div_iff₀ hr).mpr (by nlinarith)
  norm_num at hh
  rw [one_div] at hi
  linarith

lemma tfInfiniteField_singular_lower : ∃ c > 0, ∃ R > 0,
    ∀ x, x ≠ 0 → ‖x‖ ≤ R → c * CoulombPDE.radialPower (-2) x ≤ tfInfiniteField x := by
  obtain ⟨r₀, hr, hb⟩ := tf_first_field_large
  refine ⟨r₀^4, pow_pos hr _, r₀, hr, ?_⟩
  intro x hx hxr
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let a := r₀/‖x‖
  have ha : 1 ≤ a := (one_le_div hn).mpr hxr
  have he : ‖a • x‖ = ‖r₀ • radialAxis‖ := by
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ha), TFUnitData.ray_norm hr]
    exact div_mul_cancel₀ _ hn.ne'
  have hval := (tfIncreasingData 0).field_radial _ _ he
  have hc := tfInfiniteField_dominates_dilation ha x hx
  rw [CoulombPDE.shiftedDilation, hval] at hc
  have hp : a^4 ≤ tfInfiniteField x := by nlinarith [pow_nonneg (zero_le_one.trans ha) 4]
  have ht : a^4 = r₀^4 * CoulombPDE.radialPower (-2) x := by
    have hmul := CoulombPDE.norm_four_mul_radialPower hx
    dsimp [a]
    rw [div_pow, div_eq_iff (pow_ne_zero _ hn.ne')]
    calc
      r₀^4 = r₀^4 * (‖x‖^4 * CoulombPDE.radialPower (-2) x) := by rw [hmul, mul_one]
      _ = _ := by ring
  rwa [ht] at hp

theorem tfInfiniteField_singularProfile : CoulombPDE.SingularProfile tfReactionCoefficient tfInfiniteField := by
  refine ⟨fun _ hx => (tfInfiniteField_classical hx).1,
    fun _ hx => (tfInfiniteField_classical hx).2, tfInfiniteField_decay, ?_⟩
  obtain ⟨c, hc, R, hR, hl⟩ := tfInfiniteField_singular_lower
  let A := CoulombPDE.sommerfeldCoefficient tfReactionCoefficient
  have hA : 0 < A := CoulombPDE.sommerfeldCoefficient_pos tfReactionCoefficient_pos
  refine ⟨c, hc, A+1, by linarith, min R 1, lt_min hR zero_lt_one,
    fun x hx hr => hl x hx (hr.trans (min_le_left _ _)), ?_⟩
  intro x hx hr
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu := tfInfiniteRadial_upper hn
  have hmul := CoulombPDE.norm_four_mul_radialPower hx
  have hpow : ‖x‖^4 ≤ 1 := by
    exact pow_le_one₀ (norm_nonneg x) (hr.trans (min_le_right _ _))
  have hrp := CoulombPDE.radialPower_pos (-2) hx
  have hlow : 1 ≤ CoulombPDE.radialPower (-2) x := by nlinarith
  have he : A / ‖x‖^4 = A * CoulombPDE.radialPower (-2) x := by
    apply (div_eq_iff (pow_ne_zero _ hn.ne')).mpr
    nlinarith
  change tfInfiniteField x ≤ 1 + A / ‖x‖^4 at hu
  rw [he] at hu
  nlinarith


open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

def tfSupportRadius : ℝ := TFUnitData.chargeCap 1 + 2

lemma tfSupportRadius_gt_one : 1 < tfSupportRadius := by
  have := TFUnitData.chargeCap_pos (show (0:ℝ) < 1 by norm_num)
  unfold tfSupportRadius
  linarith

lemma TFUnitData.uniform_support {Z : ℝ} (D : TFUnitData Z) (hZ : 0 < Z)
    (x : TFSpace) (hx : tfSupportRadius ≤ ‖x‖) : D.density x = 0 := by
  have hn : 0 < ‖x‖ := (zero_lt_one.trans tfSupportRadius_gt_one).trans_le hx
  have hh := D.radialField_far_bound hZ (show (0:ℝ) < 1 by norm_num)
    ((tfSupportRadius_gt_one.le).trans hx)
  rw [D.radialField_eq hZ (norm_pos_iff.mp hn)] at hh
  have hu : D.field x ≤ 1 := hh.trans ((div_le_one hn).mpr (by
    have hp := TFUnitData.chargeCap_pos (show (0:ℝ) < 1 by norm_num)
    unfold tfSupportRadius at hx
    linarith))
  rw [D.euler, tfEulerDensity, show tfField Z D.density x = D.field x from rfl,
    max_eq_right (by linarith : D.field x - 1 ≤ 0), zero_div]
  exact Real.zero_rpow (by norm_num)

lemma TFUnitData.exterior_field {Z r : ℝ} (D : TFUnitData Z) (hZ : 0 < Z)
    (hr : tfSupportRadius ≤ r) : D.radialField r = (Z-D.mass)/r := by
  have hr0 : 0 < r := (zero_lt_one.trans tfSupportRadius_gt_one).trans_le hr
  rw [D.radialField_ray hZ hr0, TFUnitData.field, tfField]
  rw [tfPotential_newton_exterior_closed D.admissible.2.1 (tfAdmissible_memLp D.admissible)
    D.radial (zero_lt_one.trans tfSupportRadius_gt_one)
    (fun y hy => le_of_not_gt (fun hh => hy (D.uniform_support hZ y hh.le)))
    (by rw [TFUnitData.ray_norm hr0]; exact hr)]
  rw [D.admissible.2.2.1, TFUnitData.ray_norm hr0, sub_div]

lemma TFUnitData.radialField_le_infinite {Z r : ℝ} (D : TFUnitData Z)
    (hZ : 0 < Z) (hr : 0 < r) : D.radialField r ≤ tfInfiniteRadial r := by
  obtain ⟨n, hn⟩ := exists_nat_gt Z
  have hh := (D.finiteProfile hZ).compare ((tfIncreasingData n).finiteProfile (by positivity))
    tfReactionCoefficient_pos.le (show Z < (n:ℝ)+1 by linarith)
    (r • radialAxis) (TFUnitData.ray_ne_zero hr)
  rw [← D.radialField_ray hZ hr, ← (tfIncreasingData n).radialField_ray (by positivity) hr] at hh
  exact hh.trans (tfIncreasingField_le hr n)

def tfRealRadial (Z r : ℝ) : ℝ := if hZ : 0 < Z then (tfUnitData Z hZ).radialField r else 0
def tfUnitDeficit (Z : ℝ) : ℝ := if hZ : 0 < Z then Z-(tfUnitData Z hZ).mass else 0

lemma tfRealRadial_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun Z => tfRealRadial Z r) atTop (𝓝 (tfInfiniteRadial r)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨n, hn⟩ := (eventually_atTop.1 ((tendsto_order.1 (tfIncreasingField_tendsto hr)).1 a ha))
    filter_upwards [eventually_gt_atTop ((n:ℝ)+1)] with Z hZ
    have hZ0 : 0 < Z := (by positivity : (0:ℝ) < n+1).trans hZ
    rw [tfRealRadial, dite_eq_left hZ0]
    have hh := ((tfIncreasingData n).finiteProfile (by positivity)).compare
      ((tfUnitData Z hZ0).finiteProfile hZ0) tfReactionCoefficient_pos.le hZ
      (r • radialAxis) (TFUnitData.ray_ne_zero hr)
    rw [← (tfIncreasingData n).radialField_ray (by positivity) hr,
      ← (tfUnitData Z hZ0).radialField_ray hZ0 hr] at hh
    exact (hn n le_rfl).trans_le hh
  · intro a ha
    filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
    rw [tfRealRadial, dite_eq_left hZ]
    exact ((tfUnitData Z hZ).radialField_le_infinite hZ hr).trans_lt ha

def tfResidualCharge : ℝ := tfSupportRadius * tfInfiniteRadial tfSupportRadius

lemma tfResidualCharge_pos : 0 < tfResidualCharge := by
  have hr := zero_lt_one.trans tfSupportRadius_gt_one
  have hp := tfInfiniteField_singularProfile.pos tfReactionCoefficient_pos
    (tfSupportRadius • radialAxis) (TFUnitData.ray_ne_zero hr)
  rw [tfInfiniteField, TFUnitData.ray_norm hr] at hp
  exact mul_pos hr hp

lemma TFUnitData.deficit_eq {Z : ℝ} (D : TFUnitData Z) (hZ : 0 < Z) :
    Z-D.mass = tfSupportRadius * D.radialField tfSupportRadius := by
  rw [D.exterior_field hZ le_rfl]
  exact (mul_div_cancel₀ _ (zero_lt_one.trans tfSupportRadius_gt_one).ne').symm

theorem tf_unit_deficit_tendsto : Tendsto tfUnitDeficit atTop (𝓝 tfResidualCharge) := by
  have ht := (tfRealRadial_tendsto (zero_lt_one.trans tfSupportRadius_gt_one)).const_mul tfSupportRadius
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
  rw [tfRealRadial, tfUnitDeficit, dite_eq_left hZ, dite_eq_left hZ]
  exact ((tfUnitData Z hZ).deficit_eq hZ).symm

lemma tfUnitDeficit_nonneg (Z : ℝ) : 0 ≤ tfUnitDeficit Z := by
  unfold tfUnitDeficit
  split_ifs with hZ
  · exact sub_nonneg.mpr ((tfUnitData Z hZ).mass_le_charge hZ)
  · exact le_rfl

lemma tfUnitDeficit_le (Z : ℝ) : tfUnitDeficit Z ≤ TFUnitData.chargeCap 1 := by
  by_cases hZ : 0 < Z
  · rw [tfUnitDeficit, dite_eq_left hZ, (tfUnitData Z hZ).deficit_eq hZ]
    have hh := (tfUnitData Z hZ).radialField_far_bound hZ (show (0:ℝ) < 1 by norm_num)
      tfSupportRadius_gt_one.le
    have hr := zero_lt_one.trans tfSupportRadius_gt_one
    calc
      _ ≤ tfSupportRadius * (TFUnitData.chargeCap 1 / tfSupportRadius) := mul_le_mul_of_nonneg_left hh hr.le
      _ = _ := mul_div_cancel₀ _ hr.ne'
  · rw [tfUnitDeficit, dite_eq_right hZ]
    exact (TFUnitData.chargeCap_pos (show (0:ℝ) < 1 by norm_num)).le

end

open MeasureTheory Filter Set Metric Topology

end CoulombAnalysis

end

end OAI
