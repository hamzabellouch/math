import OAI.GroupTheory.PolycyclicRecognition.Analysis.OccupationSampling
import Mathlib.Topology.UrysohnsLemma

namespace OAI

/-! # Compact probability cutoffs for occupation and segment sampling -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Filter
open scoped Topology

/-- A compact subset of an open chart admits a continuous compactly
supported probability density which is one fixed positive constant on that
subset. It is bounded above by that same constant everywhere. -/
theorem exists_compact_probability_density
    {X : Type*} [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    {K U : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (ρ : C(X, ℝ)) (b : ℝ), 0 < b ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧
      (∀ x, 0 ≤ ρ x ∧ ρ x ≤ b) ∧ (∀ x ∈ K, ρ x = b) ∧
      Integrable ρ μ ∧ ∫ x, ρ x ∂μ = 1 := by
  obtain ⟨f, hfK, hfcomp, hfU, hf⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hfi : Integrable f μ := f.continuous.integrable_of_hasCompactSupport hfcomp
  obtain ⟨x, hx⟩ := hne
  have hx1 : f x = 1 := hfK hx
  have hmass : 0 < ∫ x, f x ∂μ :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfcomp
      (fun y => (hf y).1) (by rw [hx1]; norm_num)
  let b := (∫ x, f x ∂μ)⁻¹
  let ρ : C(X, ℝ) := ⟨fun x => b * f x, continuous_const.mul f.continuous⟩
  have hb : 0 < b := inv_pos.mpr hmass
  have hsub : tsupport ρ ⊆ tsupport f := tsupport_mul_subset_right
  have hcomp : HasCompactSupport ρ := hfcomp.of_isClosed_subset (isClosed_tsupport ρ) hsub
  refine ⟨ρ, b, hb, hcomp, hsub.trans hfU, ?_, ?_, ?_, ?_⟩
  · intro y
    exact ⟨mul_nonneg hb.le (hf y).1, by
      change b * f y ≤ b
      nlinarith [(hf y).2]⟩
  · intro y hy
    change b * f y = b
    rw [hfK hy, Pi.one_apply, mul_one]
  · exact ρ.continuous.integrable_of_hasCompactSupport hcomp
  · change (∫ x, b * f x ∂μ) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hmass.ne'

/-- Every point where the continuous density is positive belongs to the
support of its probability measure. -/
theorem mem_support_densityProbabilityMeasure
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] (ρ : X → ℝ) (hρ : Continuous ρ)
    (hi : Integrable ρ μ) (hp : ∀ x, 0 ≤ ρ x) (hm : ∫ x, ρ x ∂μ = 1)
    {x : X} (hx : 0 < ρ x) :
    x ∈ (densityProbabilityMeasure μ ρ hi hp hm : Measure X).support := by
  apply (Measure.mem_support_iff_forall x).mpr
  intro U hU
  apply pos_iff_ne_zero.mpr
  intro hzero
  change μ.withDensity (fun y => ENNReal.ofReal (ρ y)) U = 0 at hzero
  have hz := (withDensity_apply_eq_zero hρ.measurable.ennreal_ofReal).mp hzero
  have hpos : 0 < μ ({y | 0 < ρ y} ∩ U) := μ.measure_pos_of_mem_nhds
    (inter_mem (hρ.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)) hU)
  apply hpos.ne'
  apply measure_mono_null _ hz
  intro y hy
  exact ⟨(ENNReal.ofReal_pos.mpr hy.1).ne', hy.2⟩

end PolycyclicRecognition

end

end OAI
