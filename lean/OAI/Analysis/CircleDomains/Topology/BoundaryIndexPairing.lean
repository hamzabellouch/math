import OAI.Analysis.CircleDomains.Topology.PeriodicBoundaryPairing
import OAI.Analysis.CircleDomains.Topology.BoundaryIndexMean
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! The boundary pairing of the actual averaged index is integration
against the starting-angle law. This proves the weak boundary identity
used when a smooth inner contour approaches the original boundary. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem integral_single_boundary_index
    (φ dφ : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : Continuous dφ)
    (a : UnitAddCircle) :
    (∫ x in (0 : ℝ)..1, dφ x * (⌊x - unitCircleCut a⌋ : ℝ)) =
      φ 0 - φ (unitCircleCut a) := by
  let t := unitCircleCut a
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨(unitCircleCut_mem a).1, (unitCircleCut_mem a).2.le⟩
  have he : (fun x => dφ x * (⌊x - t⌋ : ℝ)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x => -((Iic t).indicator dφ x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc (0 : ℝ) 1)).ae_ne 1,
      (volume.restrict (Ioc (0 : ℝ) 1)).ae_ne t] with x hx hx1 hxt
    by_cases hlt : x < t
    · have hfloor : ⌊x - t⌋ = (-1 : ℤ) := by
        apply Int.floor_eq_iff.mpr
        constructor <;> norm_num
        · linarith [ht.2, hx.1]
        · linarith
      simp only [hfloor, Int.cast_neg, Int.cast_one, mul_neg, mul_one,
        indicator_of_mem (show x ∈ Iic t from hlt.le)]
    · have htx : t < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hxt)
      have hfloor : ⌊x - t⌋ = (0 : ℤ) := by
        apply Int.floor_eq_iff.mpr
        constructor <;> norm_num
        · linarith
        · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
          linarith [ht.1]
      simp only [hfloor, Int.cast_zero, mul_zero,
        indicator_of_notMem (show x ∉ Iic t from not_le_of_gt htx), neg_zero]
  have hEq : (∫ x in (0 : ℝ)..1, dφ x * (⌊x - t⌋ : ℝ)) =
      -(∫ x in (0 : ℝ)..t, dφ x) := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      integral_congr_ae he, integral_neg,
      ← intervalIntegral.integral_of_le zero_le_one]
    exact congrArg Neg.neg (intervalIntegral.integral_indicator (f := dφ) (μ := volume) ht)
  rw [hEq, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hφ x) (hdφ.intervalIntegrable 0 t)]
  ring

 theorem integrable_weighted_boundary_index
    (β : ProbabilityMeasure UnitAddCircle) (dφ : ℝ → ℝ) (hdφ : Continuous dφ) :
    Integrable (fun p : ℝ × UnitAddCircle => dφ p.1 * (⌊p.1 - unitCircleCut p.2⌋ : ℝ))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (β : Measure UnitAddCircle)) := by
  have hidx : Measurable (fun p : ℝ × UnitAddCircle => (⌊p.1 - unitCircleCut p.2⌋ : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      (measurable_fst.sub (measurable_unitCircleCut.comp measurable_snd)).floor
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hdφ.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg (dφ 0)).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  have hfirst : ∀ᵐ p : ℝ × UnitAddCircle
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (β : Measure UnitAddCircle)),
      p.1 ∈ Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx => Eventually.of_forall fun _ => hx
  apply Integrable.of_bound ((hdφ.measurable.comp measurable_fst).mul hidx).aestronglyMeasurable
    (C * 3)
  filter_upwards [hfirst] with p hp
  have hcount : |(⌊p.1 - unitCircleCut p.2⌋ : ℝ)| ≤ 3 := by
    have hb := boundaryIndex_bound p.1 p.2
    have habs : |p.1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1], hp.2⟩
    linarith
  change ‖dφ p.1 * (⌊p.1 - unitCircleCut p.2⌋ : ℝ)‖ ≤ C * 3
  rw [norm_mul, Real.norm_eq_abs (⌊p.1 - unitCircleCut p.2⌋ : ℝ)]
  exact mul_le_mul (hC p.1 ⟨hp.1.le, hp.2⟩) hcount (abs_nonneg _) hC0

 theorem integral_weighted_boundaryIndexMean
    (β : ProbabilityMeasure UnitAddCircle) (φ dφ : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : Continuous dφ) :
    (∫ x in (0 : ℝ)..1, dφ x * boundaryIndexMean β x) =
      ∫ a, φ 0 - φ (unitCircleCut a) ∂(β : Measure UnitAddCircle) := by
  have hF := integrable_weighted_boundary_index β dφ hdφ
  rw [intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ x, ∫ a, dφ x * (⌊x - unitCircleCut a⌋ : ℝ)
        ∂(β : Measure UnitAddCircle) ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change dφ x * (∫ a, (⌊x - unitCircleCut a⌋ : ℝ) ∂(β : Measure UnitAddCircle)) = _
      exact (integral_const_mul (dφ x) (fun a => (⌊x - unitCircleCut a⌋ : ℝ))).symm
    _ = ∫ a, ∫ x, dφ x * (⌊x - unitCircleCut a⌋ : ℝ)
        ∂(volume.restrict (Ioc (0 : ℝ) 1)) ∂(β : Measure UnitAddCircle) :=
      integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro a
      simpa only [intervalIntegral.integral_of_le zero_le_one] using
        integral_single_boundary_index φ dφ hφ hdφ a

 theorem liftedBoundaryPairing_boundaryIndexMean
    (β : ProbabilityMeasure UnitAddCircle) (φ dφ : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : Continuous dφ)
    (hperiod : φ 1 = φ 0) :
    liftedBoundaryPairing φ dφ (boundaryIndexMean β) =
      ∫ a, φ (unitCircleCut a) ∂(β : Measure UnitAddCircle) := by
  have hc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  have hi : Integrable (fun a : UnitAddCircle => φ (unitCircleCut a))
      (β : Measure UnitAddCircle) := by
    apply Integrable.of_bound (hc.measurable.comp measurable_unitCircleCut).aestronglyMeasurable C
    exact Eventually.of_forall fun a => hC _ ⟨(unitCircleCut_mem a).1, (unitCircleCut_mem a).2.le⟩
  have hb : boundaryIndexMean β 1 = boundaryIndexMean β 0 + 1 := by
    simpa only [zero_add] using boundaryIndexMean_add_one β 0
  unfold liftedBoundaryPairing
  rw [hperiod, integral_weighted_boundaryIndexMean β φ dφ hφ hdφ,
    integral_sub (integrable_const (φ 0)) hi, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hb]
  ring

end CircleDomainRigidity

end

end OAI
