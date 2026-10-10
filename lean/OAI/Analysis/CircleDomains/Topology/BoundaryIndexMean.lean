import OAI.Analysis.CircleDomains.Topology.DiskArcBoundary
import OAI.Analysis.CircleDomains.Topology.CircleQuantileArcs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

/-! Averaging the proved boundary indices against an atomless starting
law gives a continuous boundary coordinate with positive period one. -/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer

def boundaryIndexMean (β : ProbabilityMeasure UnitAddCircle) (x : ℝ) : ℝ :=
  ∫ a, (⌊x - unitCircleCut a⌋ : ℝ) ∂(β : Measure UnitAddCircle)

lemma measurable_boundaryIndex (x : ℝ) :
    Measurable (fun a : UnitAddCircle => (⌊x - unitCircleCut a⌋ : ℝ)) :=
  (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
    (measurable_const.sub measurable_unitCircleCut).floor

lemma boundaryIndex_bound (x : ℝ) (a : UnitAddCircle) :
    |(⌊x - unitCircleCut a⌋ : ℝ)| ≤ |x| + 2 := by
  have ha := unitCircleCut_mem a
  have hlo := Int.floor_le (x - unitCircleCut a)
  have hhi := Int.lt_floor_add_one (x - unitCircleCut a)
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2, le_abs_self x, neg_abs_le x]

lemma integrable_boundaryIndex (β : ProbabilityMeasure UnitAddCircle) (x : ℝ) :
    Integrable (fun a : UnitAddCircle => (⌊x - unitCircleCut a⌋ : ℝ))
      (β : Measure UnitAddCircle) :=
  Integrable.of_bound (measurable_boundaryIndex x).aestronglyMeasurable (|x| + 2)
    (Eventually.of_forall fun a => by simpa only [Real.norm_eq_abs] using boundaryIndex_bound x a)

lemma continuousAt_boundaryIndex (a : UnitAddCircle) (x : ℝ) (ha : a ≠ (x : UnitAddCircle)) :
    ContinuousAt (fun y : ℝ => (⌊y - unitCircleCut a⌋ : ℝ)) x := by
  let y := x - unitCircleCut a
  have hne : (⌊y⌋ : ℝ) ≠ y := by
    intro h
    have hx : x = unitCircleCut a + (⌊y⌋ : ℝ) := by dsimp [y] at h; linarith
    apply ha
    rw [hx, AddCircle.coe_add]
    have hn : ((⌊y⌋ : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (⌊y⌋ : ℝ) 0).mpr ⟨⌊y⌋, by simp⟩
    rw [hn, add_zero]
    exact AddCircle.coe_equivIco.symm
  have hy : (⌊y⌋ : ℝ) < y := lt_of_le_of_ne (Int.floor_le y) hne
  have hn : Ico (⌊y⌋ : ℝ) ((⌊y⌋ : ℝ) + 1) ∈ 𝓝 y :=
    mem_of_superset (Ioo_mem_nhds hy (Int.lt_floor_add_one y)) Ioo_subset_Ico_self
  exact ((continuousOn_floor ⌊y⌋).continuousAt hn).comp
    (f := fun z : ℝ => z - unitCircleCut a) (continuous_id.sub continuous_const).continuousAt

theorem continuous_boundaryIndexMean (β : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (β : Measure UnitAddCircle)] : Continuous (boundaryIndexMean β) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := fun _ => |x| + 3)
  · exact Eventually.of_forall fun y => (measurable_boundaryIndex y).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    apply Eventually.of_forall
    intro a
    have hd : |y - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
    have hb := boundaryIndex_bound y a
    have ha : |y| ≤ |y - x| + |x| := by
      simpa only [sub_add_cancel] using abs_add_le (y - x) x
    simpa only [Real.norm_eq_abs] using (show |(⌊y - unitCircleCut a⌋ : ℝ)| ≤ |x| + 3 by linarith)
  · exact integrable_const _
  · have ha : ∀ᵐ a ∂(β : Measure UnitAddCircle), a ≠ (x : UnitAddCircle) := by
      exact ae_iff.mpr (by simp)
    exact ha.mono fun a h => continuousAt_boundaryIndex a x h

theorem boundaryIndexMean_add_one (β : ProbabilityMeasure UnitAddCircle) (x : ℝ) :
    boundaryIndexMean β (x + 1) = boundaryIndexMean β x + 1 := by
  have he : (fun a : UnitAddCircle => (⌊x + 1 - unitCircleCut a⌋ : ℝ)) =
      fun a => (⌊x - unitCircleCut a⌋ : ℝ) + 1 := by
    funext a
    rw [show x + 1 - unitCircleCut a = (x - unitCircleCut a) + 1 by ring,
      Int.floor_add_one, Int.cast_add, Int.cast_one]
  simp only [boundaryIndexMean, he, integral_add (integrable_boundaryIndex β x)
    (integrable_const 1), integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]

theorem boundaryIndexMean_eq_cdf_sub_one (β : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (β : Measure UnitAddCircle)] {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    boundaryIndexMean β x = cdf (β.map unitCircleCut : Measure ℝ) x - 1 := by
  let S : Set UnitAddCircle := {a | unitCircleCut a ≤ x}
  have hS : MeasurableSet S := measurable_unitCircleCut measurableSet_Iic
  have hpos : ∀ᵐ a ∂(β : Measure UnitAddCircle), 0 < unitCircleCut a := by
    have ha : ∀ᵐ a ∂(β : Measure UnitAddCircle), a ≠ 0 := ae_iff.mpr (by simp)
    filter_upwards [ha] with a ha
    apply lt_of_le_of_ne (unitCircleCut_mem a).1
    intro he
    apply ha
    have hp : (unitCircleCut a : UnitAddCircle) = a := AddCircle.coe_equivIco
    simpa only [he.symm, AddCircle.coe_zero] using hp.symm
  have he : (fun a : UnitAddCircle => (⌊x - unitCircleCut a⌋ : ℝ)) =ᵐ[(β : Measure UnitAddCircle)]
      fun a => S.indicator (fun _ => (1 : ℝ)) a - 1 := by
    filter_upwards [hpos] with a ha
    have hlt := (unitCircleCut_mem a).2
    by_cases hax : unitCircleCut a ≤ x
    · have hf : ⌊x - unitCircleCut a⌋ = (0 : ℤ) :=
        Int.floor_eq_iff.mpr ⟨by simp only [Int.cast_zero]; linarith,
          by simp only [Int.cast_zero]; linarith [hx.2]⟩
      simp [S, hax, hf]
    · have hf : ⌊x - unitCircleCut a⌋ = (-1 : ℤ) :=
        Int.floor_eq_iff.mpr ⟨by norm_num; linarith [hx.1],
          by norm_num; linarith [lt_of_not_ge hax]⟩
      simp [S, hax, hf]
  calc
    boundaryIndexMean β x = ∫ a, S.indicator (fun _ => (1 : ℝ)) a - 1 ∂(β : Measure UnitAddCircle) :=
      integral_congr_ae he
    _ = (β : Measure UnitAddCircle).real S - 1 := by
      rw [integral_sub ((integrable_const 1).indicator hS) (integrable_const 1)]
      change (∫ a, S.indicator (1 : UnitAddCircle → ℝ) a ∂(β : Measure UnitAddCircle)) -
        (∫ _a : UnitAddCircle, (1 : ℝ) ∂(β : Measure UnitAddCircle)) = _
      rw [integral_indicator_one hS, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    _ = cdf (β.map unitCircleCut : Measure ℝ) x - 1 := by
      rw [cdf_eq_real]
      simp only [measureReal_def]
      rw [ProbabilityMeasure.map_apply' β
        measurable_unitCircleCut.aemeasurable measurableSet_Iic]
      rfl

theorem boundaryIndexMean_increment_measure (β : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (β : Measure UnitAddCircle)] {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (boundaryIndexMean β y - boundaryIndexMean β x) =
      (β.map unitCircleCut : Measure ℝ) (Ioc x y) := by
  rw [boundaryIndexMean_eq_cdf_sub_one β hx, boundaryIndexMean_eq_cdf_sub_one β hy]
  simp only [sub_sub_sub_cancel_right]
  calc
    _ = (cdf (β.map unitCircleCut : Measure ℝ)).measure (Ioc x y) :=
      ((cdf (β.map unitCircleCut : Measure ℝ)).measure_Ioc x y).symm
    _ = _ := by rw [measure_cdf]

end CircleDomainRigidity

end

end OAI
