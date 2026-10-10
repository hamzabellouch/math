import Mathlib
import OAI.Geometry.CAT0Fillings.Density.InverseCutoff
import OAI.Geometry.CAT0Fillings.Minimizers.SpatialVariation

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

noncomputable def cutoffVariationWeight (ε r a : ℝ) : ℝ :=
  if r < ε then 2 else 2*inverseSquareCutoff ε r*(1-a)

lemma cutoffVariationWeight_bounds {ε r a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (0:ℝ) 1) :
    0 ≤ cutoffVariationWeight ε r a ∧ cutoffVariationWeight ε r a ≤ 2 := by
  unfold cutoffVariationWeight
  split_ifs
  · norm_num
  · have hg := inverseSquareCutoff_nonneg (ε := ε) r
    have hgl := inverseSquareCutoff_le_one hε r
    have hh := mul_le_mul_of_nonneg_left (show 1-a ≤ 1 by linarith [ha.1])
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hg)
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) hg) (sub_nonneg.mpr ha.2)
    · nlinarith [ha.2]

lemma cutoff_pointwise_estimate {ε ell r a : ℝ} (hε : 0 < ε) (hell : 0 < ell)
    (hr : 0 ≤ r) (ha : a ∈ Icc (0:ℝ) 1) :
    (if r < ε then 2*ell-ε else 0)-ε^2/(8*ell) ≤
      ell*cutoffVariationWeight ε r a-r*inverseSquareCutoff ε r*Real.sqrt (1-a) := by
  have hs0 := Real.sqrt_nonneg (1-a)
  have hs2 : (Real.sqrt (1-a))^2 = 1-a := Real.sq_sqrt (sub_nonneg.mpr ha.2)
  have hs1 : Real.sqrt (1-a) ≤ 1 := by nlinarith [ha.1]
  by_cases ht : r < ε
  · simp only [cutoffVariationWeight,ite_eq_left ht,inverseSquareCutoff_eq_one hε ht.le,mul_one]
    have hh := mul_le_mul_of_nonneg_left hs1 hr
    have hend : 0 ≤ ε^2/(8*ell) := by positivity
    nlinarith
  · have hr0 : 0 < r := hε.trans_le (le_of_not_gt ht)
    let b : ℝ := Real.sqrt (1-a)/r
    have hquad : 2*ell*b^2-b ≥ -1/(8*ell) := by
      have hh : b-2*ell*b^2 ≤ 1/(8*ell) := by
        apply (le_div_iff₀ (by positivity : 0 < 8*ell)).mpr
        nlinarith [sq_nonneg (4*ell*b-1)]
      simpa only [neg_sub,neg_div] using neg_le_neg hh
    have he : ell*cutoffVariationWeight ε r a-r*inverseSquareCutoff ε r*Real.sqrt (1-a) =
        ε^2*(2*ell*b^2-b) := by
      simp only [cutoffVariationWeight,ite_eq_right ht,inverseSquareCutoff,max_eq_right (le_of_not_gt ht),b]
      field_simp
      nlinarith [hs2]
    rw [he,ite_eq_right ht,zero_sub]
    have hh := mul_le_mul_of_nonneg_left hquad (sq_nonneg ε)
    calc
      -(ε^2/(8*ell)) = ε^2*(-1/(8*ell)) := by ring
      _ ≤ ε^2*(2*ell*b^2-b) := hh

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_density_zero_or_not_mem {s : Set X} (hs : MeasurableSet s)
    (hμ : MassMeasure.currentMassMeasure hT s = 0) (i : ℕ) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      q.density i z = 0 ∨ (q.chart i).paramExtended z ∉ s := by
  classical
  let τ := densityPush (volume.restrict (q.chart i).domain) (q.chart i).paramExtended (q.density i)
  let : IsFiniteMeasure τ := densityPush_finite _ _ (q.density_integrable i)
  have ht : τ ≤ MassMeasure.currentMassMeasure hT := by
    rw [q.measure_eq]
    exact Measure.le_sum (fun index => densityPush (volume.restrict (q.chart index).domain)
      (q.chart index).paramExtended (q.density index)) i
  have ht0 : τ s = 0 := le_antisymm ((ht s).trans_eq hμ) bot_le
  have hi : ∫ z, q.density i z*s.indicator (fun _ => (1:ℝ)) ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain = 0 := by
    rw [←integral_densityPush_measurable _ (q.chart i).measurable_paramExtended
      (q.density_integrable i)
      (Eventually.of_forall fun _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (measurable_const.indicator hs),integral_indicator hs,integral_const]
    simp only [Measure.restrict_apply_univ,measureReal_def,smul_eq_mul]
    change (τ s).toReal*1 = 0
    rw [ht0]; simp
  have hB : ∃ B : ℝ, ∀ x, |s.indicator (fun _ => (1:ℝ)) x| ≤ B := by
    refine ⟨1,fun x => ?_⟩
    by_cases hx : x ∈ s <;> simp [hx]
  have ha := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun _ => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (indicator_nonneg (fun _ _ => zero_le_one) _))
    (q.weighted_density_integrable_borel i (measurable_const.indicator hs) hB)).mp hi
  filter_upwards [ha] with z hz
  by_cases hx : (q.chart i).paramExtended z ∈ s
  · left
    simpa only [density,indicator_of_mem hx,Pi.zero_apply,mul_one] using hz
  · exact Or.inr hx

lemma cutoff_weight_integrable (o : X) (i : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun z => q.density i z * cutoffVariationWeight ε
      (dist o ((q.chart i).paramExtended z)) (q.radialNormSq o i z))
      (volume.restrict (q.chart i).domain) := by
  classical
  have hr : Measurable (fun z => dist o ((q.chart i).paramExtended z)) :=
    (continuous_const.dist continuous_id).measurable.comp (q.chart i).measurable_paramExtended
  have hg : Measurable (fun z => inverseSquareCutoff ε (dist o ((q.chart i).paramExtended z))) :=
    (inverseSquareCutoff_lipschitz hε).continuous.measurable.comp hr
  have hm : AEStronglyMeasurable (fun z => cutoffVariationWeight ε
      (dist o ((q.chart i).paramExtended z)) (q.radialNormSq o i z))
      (volume.restrict (q.chart i).domain) := by
    exact AEStronglyMeasurable.piecewise (measurableSet_lt hr measurable_const)
      aestronglyMeasurable_const ((hg.aestronglyMeasurable.const_mul 2).mul
        (aestronglyMeasurable_const.sub (q.aestronglyMeasurable_radialNormSq o i).restrict))
  apply (q.density_integrable i).mul_bdd hm
  filter_upwards [q.ae_radialNormSq_bounds o i] with z hz
  have hh := cutoffVariationWeight_bounds (r := dist o ((q.chart i).paramExtended z)) hε hz
  simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2

end ChartGeometry

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {T : Functional X 2} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma radialVariationChart_cutoff (o : X) (i : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hμ : MassMeasure.currentMassMeasure hT {x | dist o x = ε} = 0) :
    q.radialVariationChart o (fun x => inverseSquareCutoff ε (dist o x)) i =
      ∫ z, q.density i z*cutoffVariationWeight ε
        (dist o ((q.chart i).paramExtended z)) (q.radialNormSq o i z)
        ∂volume.restrict (q.chart i).domain := by
  have hs : MeasurableSet {x : X | dist o x = ε} := isClosed_eq
    (continuous_const.dist continuous_id) continuous_const |>.measurableSet
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (q.chart i).borel,
    ae_uniqueDiffWithinAt volume (q.chart i).domain,
    (q.chart i).ae_differentiableWithinAt_scalar (LipschitzWith.dist_right o),
    q.ae_density_zero_or_not_mem hs hμ i] with z hz hu hr hn
  rcases hn with hn | hn
  · simp only [hn,zero_mul]
  let r := dist o ((q.chart i).paramExtended z)
  have hre : (q.chart i).scalar (dist o) z = r := by
    simp only [r,IntegerChart.scalar_eq _ hz,IntegerChart.paramExtended,dite_eq_left hz]
  have hge : (q.chart i).scalar (fun x => inverseSquareCutoff ε (dist o x)) z =
      inverseSquareCutoff ε r := by
    simp only [r,IntegerChart.scalar_eq _ hz,IntegerChart.paramExtended,dite_eq_left hz]
  have hne : r ≠ ε := hn
  change q.density i z * _ = q.density i z * cutoffVariationWeight ε r (q.radialNormSq o i z)
  rw [hge,hre]
  by_cases ht : r < ε
  · have hd := (q.chart i).fderivWithin_scalar_comp hz hu hr
      (show HasDerivAt (inverseSquareCutoff ε) 0 ((q.chart i).scalar (dist o) z) by
        rw [hre]; exact hasDerivAt_inverseSquareCutoff_lt hε ht)
    change fderivWithin ℝ ((q.chart i).scalar (fun x => inverseSquareCutoff ε (dist o x)))
      (q.chart i).domain z = _ at hd
    have hrow0 : differentialRow (0 : Euc 2 →L[ℝ] ℝ) = 0 := rfl
    simp only [hd,zero_smul,hrow0,Matrix.mulVec_zero,
      dotProduct_zero,mul_zero,add_zero,cutoffVariationWeight,ite_eq_left ht,
      inverseSquareCutoff_eq_one hε ht.le,mul_one,Nat.cast_ofNat]
  · have hgt : ε < r := lt_of_le_of_ne (le_of_not_gt ht) hne.symm
    have hd := (q.chart i).fderivWithin_scalar_comp hz hu hr
      (show HasDerivAt (inverseSquareCutoff ε) (-2*ε^2/r^3)
          ((q.chart i).scalar (dist o) z) by
        rw [hre]; exact hasDerivAt_inverseSquareCutoff_gt hε hgt)
    change fderivWithin ℝ ((q.chart i).scalar (fun x => inverseSquareCutoff ε (dist o x)))
      (q.chart i).domain z = _ at hd
    have hrow : differentialRow (fderivWithin ℝ ((q.chart i).scalar
        (fun x => inverseSquareCutoff ε (dist o x))) (q.chart i).domain z) =
        (-2*ε^2/r^3) • differentialRow (fderivWithin ℝ ((q.chart i).scalar (dist o))
          (q.chart i).domain z) := by
      rw [hd]
      ext j
      simp only [differentialRow,_root_.smul_apply,Pi.smul_apply,smul_eq_mul]
    rw [hrow,Matrix.mulVec_smul,dotProduct_smul]
    simp only [smul_eq_mul,radialNormSq,cutoffVariationWeight,ite_eq_right ht,Nat.cast_ofNat,
      inverseSquareCutoff,max_eq_right hgt.le]
    field_simp
    ring

end ChartGeometry
end CAT0Fillings
end

end OAI
