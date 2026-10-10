import OAI.Analysis.CircleDomains.Topology.BoundaryIndexMean

namespace OAI

/-! The Stieltjes measure of the averaged boundary index is precisely
the starting-point law on a lifted fundamental interval. -/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem monotone_boundaryIndexMean (β : ProbabilityMeasure UnitAddCircle) :
    Monotone (boundaryIndexMean β) := by
  intro x y hxy
  apply integral_mono (integrable_boundaryIndex β x) (integrable_boundaryIndex β y)
  intro a
  change (⌊x - unitCircleCut a⌋ : ℝ) ≤ (⌊y - unitCircleCut a⌋ : ℝ)
  exact_mod_cast Int.floor_mono (sub_le_sub_right hxy (unitCircleCut a))

def boundaryIndexStieltjes (β : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (β : Measure UnitAddCircle)] : StieltjesFunction ℝ where
  toFun := boundaryIndexMean β
  mono' := monotone_boundaryIndexMean β
  right_continuous' := fun _ => (continuous_boundaryIndexMean β).continuousAt.continuousWithinAt

theorem boundaryIndexStieltjes_unit_mass (β : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (β : Measure UnitAddCircle)] (x : ℝ) :
    (boundaryIndexStieltjes β).measure (Ioc x (x + 1)) = 1 := by
  rw [StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (boundaryIndexMean β (x + 1) - boundaryIndexMean β x) = 1
  rw [boundaryIndexMean_add_one]
  simp

theorem boundaryIndexStieltjes_restrict (β : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (β : Measure UnitAddCircle)] :
    (boundaryIndexStieltjes β).measure.restrict (Ioc (0 : ℝ) 1) =
      (β.map unitCircleCut : Measure ℝ) := by
  have heq : (boundaryIndexStieltjes β).measure.restrict (Ioc (0 : ℝ) 1) =
      (β.map unitCircleCut : Measure ℝ).restrict (Ioc (0 : ℝ) 1) := by
    apply Measure.ext_of_Ioc
    intro a b _hab
    simp only [Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc]
    by_cases h : min b 1 ≤ max a 0
    · simp only [Ioc_eq_empty_of_le h, measure_empty]
    · have hx : max a 0 ∈ Icc (0 : ℝ) 1 :=
        ⟨le_max_right _ _, ((not_le.mp h).trans_le (min_le_right _ _)).le⟩
      have hy : min b 1 ∈ Icc (0 : ℝ) 1 :=
        ⟨(le_max_right _ _).trans (not_le.mp h).le, min_le_right _ _⟩
      rw [StieltjesFunction.measure_Ioc]
      exact boundaryIndexMean_increment_measure β hx hy
  rw [heq]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff measurable_unitCircleCut.aemeasurable measurableSet_Ioc).mpr
  have ha : ∀ᵐ a ∂(β : Measure UnitAddCircle), a ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [ha] with a ha
  refine ⟨lt_of_le_of_ne (unitCircleCut_mem a).1 ?_, (unitCircleCut_mem a).2.le⟩
  intro h
  apply ha
  have hp : (unitCircleCut a : UnitAddCircle) = a := AddCircle.coe_equivIco
  simpa only [h.symm, AddCircle.coe_zero] using hp.symm

theorem boundaryIndexStieltjes_integral (β : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (β : Measure UnitAddCircle)] (φ : ℝ → ℝ) :
    ∫ x in Ioc (0 : ℝ) 1, φ x ∂(boundaryIndexStieltjes β).measure =
      ∫ x, φ x ∂(β.map unitCircleCut : Measure ℝ) := by
  rw [boundaryIndexStieltjes_restrict]

end CircleDomainRigidity

end

end OAI
