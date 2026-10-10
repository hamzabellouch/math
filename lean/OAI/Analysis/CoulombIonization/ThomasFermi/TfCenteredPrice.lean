import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfBallFunctionalConvex
import OAI.Analysis.CoulombIonization.Variational.GridIncrementError

namespace OAI

noncomputable section

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
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

lemma tfPriceDeficit_tendsto {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun Z => tfPriceDeficit Z μ) atTop (𝓝 (limitDeficit tfResidualCharge μ)) := by
  have ht : Tendsto (fun Z : ℝ => Z/μ^(3/4:ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const (Real.rpow_pos_of_pos hμ _)
  simpa only [tfPriceDeficit, limitDeficit, Function.comp_def, mul_comm (μ^(3/4:ℝ))] using
    (tf_unit_deficit_tendsto.comp ht).const_mul (μ^(3/4:ℝ))

lemma tfPriceDeficit_of_nonpos {Z μ : ℝ} (hZ : Z ≤ 0) (hμ : 0 < μ) :
    tfPriceDeficit Z μ = 0 := by
  have hz : ¬0 < Z/μ^(3/4:ℝ) := not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hZ (Real.rpow_nonneg hμ.le _))
  simp only [tfPriceDeficit, tfUnitDeficit, dite_eq_right hz, mul_zero]

def tfCenteredPrice (Z μ : ℝ) : ℝ := if 0 < Z then tfPriceValue Z μ-tfEnergy Z Z else 0

lemma tfCenteredPrice_secants (Z : ℝ) : DeficitSecants (tfCenteredPrice Z) (tfPriceDeficit Z) := by
  intro v t hv hvt
  have ht := hv.trans hvt
  by_cases hZ : 0 < Z
  · simp only [tfCenteredPrice, ite_eq_left hZ]
    have htv := tfPriceValue_secant hZ ht hv
    have hvt := tfPriceValue_secant hZ hv ht
    constructor <;> linarith
  · simp only [tfCenteredPrice, ite_eq_right hZ, tfPriceDeficit_of_nonpos (le_of_not_gt hZ) hv,
      tfPriceDeficit_of_nonpos (le_of_not_gt hZ) ht, mul_zero, sub_self, le_refl, and_self]

lemma tfCenteredPrice_bounds (Z μ : ℝ) (hμ : 0 < μ) :
    -μ*tfPriceDeficit Z μ ≤ tfCenteredPrice Z μ ∧ tfCenteredPrice Z μ ≤ 0 := by
  by_cases hZ : 0 < Z
  · simpa only [tfCenteredPrice, ite_eq_left hZ] using tfPriceValue_zero_bounds hZ hμ
  · simp [tfCenteredPrice, hZ, tfPriceDeficit_of_nonpos (le_of_not_gt hZ) hμ]

theorem tf_priced_energy_limits {t : ℝ} (ht : 0 < t) :
    Tendsto (fun Z => tfPriceValue Z t-tfEnergy Z Z) atTop (𝓝 (limitPriceEnergy tfResidualCharge t)) ∧
    Tendsto (fun Z => tfPriceValue Z t-tfEnergy Z Z+t*tfPriceDeficit Z t) atTop
      (𝓝 (limitSectorEnergy tfResidualCharge t)) := by
  have hh := priced_energy_limits_filter (l := (atTop : Filter ℝ)) (err := fun _ => 0)
    tfResidualCharge_pos.le tfCenteredPrice_secants (fun _ ht => tfPriceDeficit_tendsto ht)
    tendsto_const_nhds (fun Z v hv => by
      simpa only [neg_zero, zero_sub, neg_mul] using tfCenteredPrice_bounds Z v hv) ht
  constructor
  · apply hh.1.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
    simp [tfCenteredPrice, hZ]
  · apply hh.2.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
    simp [tfCenteredPrice, hZ]

lemma tfIonization_le_priced_max {Z u v : ℝ} (hZ : 0 < Z) (hu : 0 < u) (hv : 0 < v)
    (hdu : tfPriceDeficit Z u < 1) (hdv : 1 < tfPriceDeficit Z v) :
    tfIonization 1 Z ≤ max
      (tfPriceValue Z u-tfEnergy Z Z+u*tfPriceDeficit Z u)
      (tfPriceValue Z v-tfEnergy Z Z+v*tfPriceDeficit Z v) := by
  let P := tfPriceData hZ hu
  let Q := tfPriceData hZ hv
  let d := tfPriceDeficit Z u
  let e := tfPriceDeficit Z v
  have he : 0 < e-d := by dsimp [d,e]; linarith
  let a := (e-1)/(e-d)
  let b := (1-d)/(e-d)
  have ha : 0 ≤ a := div_nonneg (by dsimp [e]; linarith) he.le
  have hb : 0 ≤ b := div_nonneg (by dsimp [d]; linarith) he.le
  have hab : a+b=1 := by dsimp [a,b]; rw [← add_div]; convert div_self he.ne' using 1; ring
  have hP : P.mass=Z-d := by dsimp [P,d]; rw [tfPriceDeficit_eq hZ hu]; ring
  have hQ : Q.mass=Z-e := by dsimp [Q,e]; rw [tfPriceDeficit_eq hZ hv]; ring
  have hm : a*P.mass+b*Q.mass=Z-1 := by rw [hP,hQ]; dsimp [a,b]; field_simp; ring
  obtain ⟨hx, hxe⟩ := tf_compact_mix P.admissible Q.admissible P.compact Q.compact ha hb hab Z
  rw [hm] at hx
  have hle := (tfEnergy_le_trial hZ hx).trans hxe
  have h1 : tfFunctional Z P.density = tfPriceValue Z u+u*d := by rw [tfPriceValue_eq hZ hu]; dsimp [P,d]; ring
  have h2 : tfFunctional Z Q.density = tfPriceValue Z v+v*e := by rw [tfPriceValue_eq hZ hv]; dsimp [Q,e]; ring
  rw [h1,h2] at hle
  let A := tfPriceValue Z u-tfEnergy Z Z+u*d
  let B := tfPriceValue Z v-tfEnergy Z Z+v*e
  have hmax : a*A+b*B ≤ max A B := by
    calc
      _ ≤ a*max A B+b*max A B := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]
  have hmulte : (a+b)*tfEnergy Z Z = tfEnergy Z Z := by rw [hab, one_mul]
  change tfEnergy Z (Z-1)-tfEnergy Z Z ≤ max A B
  dsimp [A,B] at hmax ⊢
  nlinarith

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
