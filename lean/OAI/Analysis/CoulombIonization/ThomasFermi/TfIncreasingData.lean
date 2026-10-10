import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfReactionCoefficient

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
namespace CoulombAnalysis
open CoulombAtom

def tfIncreasingData (n : ℕ) : TFUnitData (n+1) := tfUnitData (n+1) (by positivity)
def tfIncreasingField (n : ℕ) : ℝ → ℝ := (tfIncreasingData n).radialField
def tfIncreasingCharge (n : ℕ) : ℝ → ℝ := (tfIncreasingData n).charge
def tfInfiniteRadial (r : ℝ) : ℝ := ⨆ n, tfIncreasingField n r

lemma tfIncreasingField_monotone {r : ℝ} (hr : 0 < r) : Monotone (fun n => tfIncreasingField n r) := by
  intro n m hnm
  rcases hnm.eq_or_lt with h | h
  · subst h; rfl
  · have hh := ((tfIncreasingData n).finiteProfile (by positivity)).compare
      ((tfIncreasingData m).finiteProfile (by positivity)) tfReactionCoefficient_pos.le
      (show (n:ℝ)+1 < m+1 by exact_mod_cast Nat.add_lt_add_right h 1)
      (r • radialAxis) (TFUnitData.ray_ne_zero hr)
    rwa [← (tfIncreasingData n).radialField_ray (by positivity) hr,
      ← (tfIncreasingData m).radialField_ray (by positivity) hr] at hh

lemma tfIncreasingField_bounded {r : ℝ} (hr : 0 < r) :
    BddAbove (range (fun n => tfIncreasingField n r)) := by
  refine ⟨1 + CoulombPDE.sommerfeldCoefficient tfReactionCoefficient / r^4, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (tfIncreasingData n).radialField_upper (by positivity) hr

lemma tfIncreasingField_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
    tfIncreasingField n r ≤ tfInfiniteRadial r := le_ciSup (tfIncreasingField_bounded hr) n

lemma tfInfiniteRadial_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ tfInfiniteRadial r :=
  ((tfIncreasingData 0).radialField_nonneg (by positivity) hr).trans (tfIncreasingField_le hr 0)

lemma tfIncreasingField_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => tfIncreasingField n r) atTop (𝓝 (tfInfiniteRadial r)) := by
  exact tendsto_atTop_ciSup (tfIncreasingField_monotone hr) (tfIncreasingField_bounded hr)

lemma tfInfiniteRadial_upper {r : ℝ} (hr : 0 < r) :
    tfInfiniteRadial r ≤ 1 + CoulombPDE.sommerfeldCoefficient tfReactionCoefficient / r^4 := by
  apply ciSup_le
  exact fun n => (tfIncreasingData n).radialField_upper (by positivity) hr

lemma tfInfiniteRadial_far_bound {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    tfInfiniteRadial r ≤ TFUnitData.chargeCap a / r := by
  apply ciSup_le
  exact fun n => (tfIncreasingData n).radialField_far_bound (by positivity) ha hr

lemma tfInfiniteRadial_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨TFUnitData.slopeCap a, (TFUnitData.slopeCap_pos ha).le⟩ tfInfiniteRadial (Ici a) := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro x hx y hy
  apply le_of_tendsto ((tfIncreasingField_tendsto (ha.trans_le hx)).sub
    (tfIncreasingField_tendsto (ha.trans_le hy))).norm
  exact Eventually.of_forall fun n => ((tfIncreasingData n).lipschitz (by positivity) ha).norm_sub_le hx hy

lemma tfInfiniteRadial_continuous {r : ℝ} (hr : 0 < r) : ContinuousAt tfInfiniteRadial r := by
  apply (tfInfiniteRadial_lipschitz (show 0 < r/2 by positivity)).continuousOn.continuousAt
  exact Ici_mem_nhds (by linarith)

lemma positive_uIcc {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ∈ uIcc a b) : 0 < t :=
  (lt_min ha hb).trans_le ht.1

lemma positive_uIoc {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ∈ uIoc a b) : 0 < t :=
  (lt_min ha hb).trans ht.1

lemma tf_reaction_continuous : Continuous (CoulombPDE.reaction tfReactionCoefficient) := by
  unfold CoulombPDE.reaction
  exact continuous_const.mul (((continuous_id.sub continuous_const).max continuous_const).rpow_const
    (fun _ => Or.inr (by norm_num)))

lemma tf_reaction_nonneg (v : ℝ) : 0 ≤ CoulombPDE.reaction tfReactionCoefficient v := by
  unfold CoulombPDE.reaction
  exact mul_nonneg tfReactionCoefficient_pos.le (Real.rpow_nonneg (le_max_right _ _) _)

def tfFluxSource (r : ℝ) : ℝ := r^2 * CoulombPDE.reaction tfReactionCoefficient (tfInfiniteRadial r)
def tfFiniteSource (n : ℕ) (r : ℝ) : ℝ := r^2 * CoulombPDE.reaction tfReactionCoefficient (tfIncreasingField n r)

lemma tfFluxSource_continuous {r : ℝ} (hr : 0 < r) : ContinuousAt tfFluxSource r :=
  (continuousAt_id.pow 2).mul (tf_reaction_continuous.continuousAt.comp (tfInfiniteRadial_continuous hr))

lemma tfFiniteSource_continuous (n : ℕ) {r : ℝ} (hr : 0 < r) : ContinuousAt (tfFiniteSource n) r :=
  (continuousAt_id.pow 2).mul (tf_reaction_continuous.continuousAt.comp
    ((tfIncreasingData n).radialField_hasDerivAt hr).continuousAt)

lemma tfFluxSource_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable tfFluxSource volume a b :=
  (show ContinuousOn tfFluxSource (uIcc a b) from
    fun _ ht => (tfFluxSource_continuous (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSource_intervalIntegrable (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (tfFiniteSource n) volume a b :=
  (show ContinuousOn (tfFiniteSource n) (uIcc a b) from
    fun _ ht => (tfFiniteSource_continuous n (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSource_integral_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n => ∫ t in a..b, tfFiniteSource n t) atTop (𝓝 (∫ t in a..b, tfFluxSource t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence tfFluxSource
  · exact Eventually.of_forall fun n =>
      (show ContinuousOn (tfFiniteSource n) (uIoc a b) from fun _ ht =>
        (tfFiniteSource_continuous n (positive_uIoc ha hb ht)).continuousWithinAt).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun n => Eventually.of_forall fun t ht => ?_
    rw [tfFiniteSource, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (tf_reaction_nonneg _))]
    exact mul_le_mul_of_nonneg_left (CoulombPDE.reaction_monotone tfReactionCoefficient_pos.le
      (tfIncreasingField_le (positive_uIoc ha hb ht) n)) (sq_nonneg t)
  · exact tfFluxSource_intervalIntegrable ha hb
  · refine Eventually.of_forall fun t ht => ?_
    exact tendsto_const_nhds.mul (tf_reaction_continuous.continuousAt.tendsto.comp
      (tfIncreasingField_tendsto (positive_uIoc ha hb ht)))

lemma tfIncreasingCharge_integral (n : ℕ) {r : ℝ} (hr : 0 < r) :
    tfIncreasingCharge n r = tfIncreasingCharge n 1 - ∫ t in (1:ℝ)..r, tfFiniteSource n t := by
  have hd (t : ℝ) (ht : t ∈ uIcc (1:ℝ) r) :
      HasDerivAt (fun x => -tfIncreasingCharge n x) (tfFiniteSource n t) t := by
    convert ((tfIncreasingData n).charge_equation (positive_uIcc zero_lt_one hr ht) (by positivity)).neg using 1 <;> (try rfl)
    unfold tfFiniteSource tfIncreasingField
    ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (tfFiniteSource_intervalIntegrable n zero_lt_one hr)
  change (∫ t in (1:ℝ)..r, tfFiniteSource n t) = -(tfIncreasingCharge n r) - -(tfIncreasingCharge n 1) at hh
  linarith

structure TFChargeAnchor where
  charge : ℝ
  index : ℕ → ℕ
  strict : StrictMono index
  limit : Tendsto (fun n => tfIncreasingCharge (index n) 1) atTop (𝓝 charge)

lemma tfChargeAnchor_nonempty : Nonempty TFChargeAnchor := by
  obtain ⟨q, _, κ, hk, hl⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) (TFUnitData.chargeCap 1))).tendsto_subseq
    (fun n => ⟨(tfIncreasingData n).charge_nonneg (by positivity) 1,
      (tfIncreasingData n).charge_le_cap (by positivity) zero_lt_one le_rfl⟩)
  exact ⟨⟨q, κ, hk, hl⟩⟩

def tfChargeAnchor : TFChargeAnchor := Classical.choice tfChargeAnchor_nonempty
def tfInfiniteCharge (r : ℝ) : ℝ := tfChargeAnchor.charge - ∫ t in (1:ℝ)..r, tfFluxSource t

lemma tfIncreasingCharge_subseq_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => tfIncreasingCharge (tfChargeAnchor.index n) r) atTop (𝓝 (tfInfiniteCharge r)) := by
  have hh := tfChargeAnchor.limit.sub
    ((tfFiniteSource_integral_tendsto zero_lt_one hr).comp tfChargeAnchor.strict.tendsto_atTop)
  exact hh.congr (fun n => (tfIncreasingCharge_integral _ hr).symm)

lemma tfInfiniteCharge_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ tfInfiniteCharge r := by
  exact ge_of_tendsto (tfIncreasingCharge_subseq_tendsto hr)
    (Eventually.of_forall fun n => (tfIncreasingData (tfChargeAnchor.index n)).charge_nonneg (by positivity) r)

lemma tfInfiniteCharge_cap {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    tfInfiniteCharge r ≤ TFUnitData.chargeCap a := by
  exact le_of_tendsto (tfIncreasingCharge_subseq_tendsto (ha.trans_le hr))
    (Eventually.of_forall fun n => (tfIncreasingData (tfChargeAnchor.index n)).charge_le_cap (by positivity) ha hr)

lemma tfInfiniteCharge_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt tfInfiniteCharge (-tfFluxSource r) r := by
  exact (intervalIntegral.integral_hasDerivAt_right (tfFluxSource_intervalIntegrable zero_lt_one hr)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi (fun _ ht => tfFluxSource_continuous ht) r hr)
    (tfFluxSource_continuous hr)).const_sub _

def tfInfiniteSlope (r : ℝ) : ℝ := -tfInfiniteCharge r / r^2
def tfFiniteSlope (n : ℕ) (r : ℝ) : ℝ := -tfIncreasingCharge n r / r^2

lemma tfInfiniteSlope_continuous {r : ℝ} (hr : 0 < r) : ContinuousAt tfInfiniteSlope r :=
  (tfInfiniteCharge_hasDerivAt hr).continuousAt.neg.div (continuousAt_id.pow 2) (pow_ne_zero _ hr.ne')

lemma tfFiniteSlope_continuous (n : ℕ) {r : ℝ} (hr : 0 < r) : ContinuousAt (tfFiniteSlope n) r :=
  ((tfIncreasingData n).charge_hasDerivAt hr).continuousAt.neg.div (continuousAt_id.pow 2) (pow_ne_zero _ hr.ne')

lemma tfInfiniteSlope_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable tfInfiniteSlope volume a b :=
  (show ContinuousOn tfInfiniteSlope (uIcc a b) from
    fun _ ht => (tfInfiniteSlope_continuous (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSlope_intervalIntegrable (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (tfFiniteSlope n) volume a b :=
  (show ContinuousOn (tfFiniteSlope n) (uIcc a b) from
    fun _ ht => (tfFiniteSlope_continuous n (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSlope_integral_subseq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n => ∫ t in a..b, tfFiniteSlope (tfChargeAnchor.index n) t) atTop
      (𝓝 (∫ t in a..b, tfInfiniteSlope t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => TFUnitData.slopeCap (min a b))
  · exact Eventually.of_forall fun n =>
      (show ContinuousOn (tfFiniteSlope (tfChargeAnchor.index n)) (uIoc a b) from fun _ ht =>
        (tfFiniteSlope_continuous _ (positive_uIoc ha hb ht)).continuousWithinAt).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun n => Eventually.of_forall fun t ht => ?_
    have hh := (tfIncreasingData (tfChargeAnchor.index n)).deriv_bound (by positivity) (lt_min ha hb) ht.1.le
    rwa [((tfIncreasingData (tfChargeAnchor.index n)).radialField_hasDerivAt (positive_uIoc ha hb ht)).deriv] at hh
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht => ?_
    exact (tfIncreasingCharge_subseq_tendsto (positive_uIoc ha hb ht)).neg.div tendsto_const_nhds
      (pow_ne_zero _ (positive_uIoc ha hb ht).ne')

lemma tfInfiniteRadial_integral {r : ℝ} (hr : 0 < r) :
    tfInfiniteRadial r = tfInfiniteRadial 1 + ∫ t in (1:ℝ)..r, tfInfiniteSlope t := by
  have hi (n : ℕ) : (∫ t in (1:ℝ)..r, tfFiniteSlope n t) = tfIncreasingField n r - tfIncreasingField n 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => (tfIncreasingData n).radialField_hasDerivAt (positive_uIcc zero_lt_one hr ht))
      (tfFiniteSlope_intervalIntegrable n zero_lt_one hr)
  have hl := ((tfIncreasingField_tendsto hr).sub (tfIncreasingField_tendsto zero_lt_one)).comp
    tfChargeAnchor.strict.tendsto_atTop
  have he := tendsto_nhds_unique (tfFiniteSlope_integral_subseq zero_lt_one hr)
    (hl.congr (fun n => (hi _).symm))
  linarith

lemma tfInfiniteRadial_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt tfInfiniteRadial (tfInfiniteSlope r) r := by
  have hh := (intervalIntegral.integral_hasDerivAt_right (tfInfiniteSlope_intervalIntegrable zero_lt_one hr)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi (fun _ ht => tfInfiniteSlope_continuous ht) r hr)
    (tfInfiniteSlope_continuous hr)).const_add (tfInfiniteRadial 1)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with t ht
  exact tfInfiniteRadial_integral ht

lemma tfInfiniteCharge_contDiffOn : ContDiffOn ℝ 1 tfInfiniteCharge (Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hr => (tfInfiniteCharge_hasDerivAt hr).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  apply ContinuousOn.congr (f := fun r => -tfFluxSource r)
    (fun r hr => (tfFluxSource_continuous hr).neg.continuousWithinAt)
  exact fun r hr => (tfInfiniteCharge_hasDerivAt hr).deriv

lemma tfInfiniteRadial_contDiffOn : ContDiffOn ℝ 2 tfInfiniteRadial (Ioi 0) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hr => (tfInfiniteRadial_hasDerivAt hr).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  apply ContDiffOn.congr (f := tfInfiniteSlope)
    (tfInfiniteCharge_contDiffOn.neg.div (contDiffOn_id.pow 2) (fun r hr => pow_ne_zero _ hr.ne'))
  exact fun r hr => (tfInfiniteRadial_hasDerivAt hr).deriv

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian

end

end OAI
