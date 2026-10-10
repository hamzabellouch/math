import OAI.Analysis.CircleDomains.Topology.RationalQuantileIntervals
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-! Four positively separated arcs from a fixed countable circle family. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

def unitCircleCut (θ : UnitAddCircle) : ℝ := AddCircle.equivIco 1 0 θ

theorem unitCircleCut_mem (θ : UnitAddCircle) : unitCircleCut θ ∈ Ico (0 : ℝ) 1 := by
  simpa only [unitCircleCut, zero_add] using (AddCircle.equivIco 1 0 θ).property

theorem unitCircleCut_injective : Injective unitCircleCut := by
  intro x y h
  exact (AddCircle.equivIco 1 0).injective (Subtype.ext h)

theorem continuousAt_unitCircleCut {θ : UnitAddCircle} (hθ : θ ≠ 0) :
    ContinuousAt unitCircleCut θ :=
  continuous_subtype_val.continuousAt.comp (AddCircle.continuousAt_equivIco 1 0 hθ)

theorem measurable_unitCircleCut : Measurable unitCircleCut := by
  apply measurable_of_continuousOn_compl_singleton (0 : UnitAddCircle)
  intro θ hθ
  exact (continuousAt_unitCircleCut hθ).continuousWithinAt

def rationalCircleArc (l u : ℚ) : Set UnitAddCircle :=
  unitCircleCut ⁻¹' Ioo (l : ℝ) (u : ℝ)

theorem measurableSet_rationalCircleArc (l u : ℚ) : MeasurableSet (rationalCircleArc l u) :=
  measurable_unitCircleCut measurableSet_Ioo

theorem isOpen_rationalCircleArc {l u : ℚ} (hl : 0 < l) :
    IsOpen (rationalCircleArc l u) := by
  apply isOpen_iff_mem_nhds.mpr
  intro θ hθ
  have hne : θ ≠ 0 := by
    intro he
    subst θ
    have hz : unitCircleCut 0 = 0 := by
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0) (by norm_num))
    have h := hθ.1
    rw [hz] at h
    have : (0 : ℝ) < l := by exact_mod_cast hl
    linarith
  exact (continuousAt_unitCircleCut hne).preimage_mem_nhds (isOpen_Ioo.mem_nhds hθ)

theorem nullSingletonClass_unitCircleCut_map (μ : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (μ : Measure UnitAddCircle)] :
    NullSingletonClass (μ.map unitCircleCut : Measure ℝ) := by
  constructor
  intro x
  rw [ProbabilityMeasure.map_apply' μ measurable_unitCircleCut.aemeasurable (measurableSet_singleton x)]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  apply unitCircleCut_injective
  exact ha.trans hb.symm

theorem unitCircleCut_cdf_endpoints (μ : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (μ : Measure UnitAddCircle)] :
    cdf (μ.map unitCircleCut : Measure ℝ) 0 = 0 ∧
      cdf (μ.map unitCircleCut : Measure ℝ) 1 = 1 := by
  have := nullSingletonClass_unitCircleCut_map μ
  have hzero : (μ.map unitCircleCut : Measure ℝ) (Iic 0) = 0 := by
    rw [ProbabilityMeasure.map_apply' μ measurable_unitCircleCut.aemeasurable measurableSet_Iic]
    apply measure_mono_null (t := unitCircleCut ⁻¹' {0})
    · intro θ hθ
      exact le_antisymm hθ (unitCircleCut_mem θ).1
    · apply Set.Subsingleton.measure_zero
      intro a ha b hb
      exact unitCircleCut_injective (ha.trans hb.symm)
  have hone : (μ.map unitCircleCut : Measure ℝ) (Iic 1) = 1 := by
    rw [ProbabilityMeasure.map_apply' μ measurable_unitCircleCut.aemeasurable measurableSet_Iic]
    have he : unitCircleCut ⁻¹' Iic (1 : ℝ) = univ := by
      ext θ
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (unitCircleCut_mem θ).2.le
    rw [he, measure_univ]
  constructor
  · rw [cdf_eq_real, measureReal_def, hzero, ENNReal.toReal_zero]
  · rw [cdf_eq_real, measureReal_def, hone, ENNReal.toReal_one]

/-- All four arcs can be taken from the countable rational endpoint family,
with cyclic order witnessed inside a single cut of the circle. -/
theorem exists_four_ordered_rational_circle_arcs (μ : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (μ : Measure UnitAddCircle)] :
    ∃ l u : Fin 4 → ℚ,
      (∀ i, 0 < l i ∧ l i < u i ∧ u i < 1 ∧
        (1 / 10 : ℝ≥0∞) < (μ : Measure UnitAddCircle) (rationalCircleArc (l i) (u i))) ∧
      ∀ i j, i < j → u i < l j := by
  have := nullSingletonClass_unitCircleCut_map μ
  obtain ⟨hz, ho⟩ := unitCircleCut_cdf_endpoints μ
  obtain ⟨l, u, hlu, hord⟩ := exists_four_ordered_rational_intervals_between
    (μ.map unitCircleCut : Measure ℝ) 0 1 hz ho
  refine ⟨l, u, ?_, hord⟩
  intro i
  obtain ⟨hl, hmid, hu, hmass⟩ := hlu i
  refine ⟨by exact_mod_cast hl, hmid, by exact_mod_cast hu, ?_⟩
  rw [ProbabilityMeasure.map_apply' μ measurable_unitCircleCut.aemeasurable measurableSet_Ioo] at hmass
  exact hmass

end CircleDomainRigidity

end

end OAI
