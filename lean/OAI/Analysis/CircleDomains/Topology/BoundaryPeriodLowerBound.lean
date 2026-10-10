import OAI.Analysis.CircleDomains.Topology.BoundaryIndexPairing

namespace OAI

/-! Positivity of the original starting-point boundary law survives
uniform approximation by a smooth lift with the same period. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem smooth_boundary_integral_lower_bound
    (β : ProbabilityMeasure UnitAddCircle) [NullSingletonClass (β : Measure UnitAddCircle)]
    (φ dφ u du : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : Continuous dφ) (hφperiod : φ 1 = φ 0)
    (hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt u (du x) x)
    (hdu : IntervalIntegrable du volume 0 1) (huperiod : u 1 = u 0 + 1)
    (δ c : ℝ) (hclose : ∀ x ∈ Icc (0 : ℝ) 1, |u x - boundaryIndexMean β x| ≤ δ)
    (hpositive : ∀ᵐ a : UnitAddCircle ∂(β : Measure UnitAddCircle), c ≤ φ (unitCircleCut a)) :
    c ≤ (∫ x in (0 : ℝ)..1, φ x * du x) + δ * ∫ x in (0 : ℝ)..1, |dφ x| := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hφc.continuousOn
  have hi : Integrable (fun a : UnitAddCircle => φ (unitCircleCut a))
      (β : Measure UnitAddCircle) := by
    apply Integrable.of_bound (hφc.measurable.comp measurable_unitCircleCut).aestronglyMeasurable C
    exact Eventually.of_forall fun a => hC _ ⟨(unitCircleCut_mem a).1, (unitCircleCut_mem a).2.le⟩
  have hc : c ≤ ∫ a, φ (unitCircleCut a) ∂(β : Measure UnitAddCircle) := by
    calc
      c = ∫ _a : UnitAddCircle, c ∂(β : Measure UnitAddCircle) := by simp
      _ ≤ _ := integral_mono_ae (integrable_const c) hi hpositive
  have huc : ContinuousOn u (Icc (0 : ℝ) 1) := by
    intro x hx
    exact (hu x (by simpa only [uIcc_of_le zero_le_one] using hx)).continuousAt.continuousWithinAt
  have hvperiod : boundaryIndexMean β 1 = boundaryIndexMean β 0 + 1 := by
    simpa only [zero_add] using boundaryIndexMean_add_one β 0
  have hsame : u 1 - u 0 = boundaryIndexMean β 1 - boundaryIndexMean β 0 := by
    rw [huperiod, hvperiod]
    ring
  have hs := liftedBoundaryPairing_stability φ dφ u (boundaryIndexMean β) hφperiod hsame
    huc (continuous_boundaryIndexMean β).continuousOn (hdφ.intervalIntegrable 0 1) δ hclose
  rw [liftedBoundaryPairing_eq_integral φ dφ u du (fun x _ => hφ x) hu
    (hdφ.intervalIntegrable 0 1) hdu,
    liftedBoundaryPairing_boundaryIndexMean β φ dφ hφ hdφ hφperiod] at hs
  linarith [neg_abs_le ((∫ x in (0 : ℝ)..1, φ x * du x) -
    ∫ a, φ (unitCircleCut a) ∂(β : Measure UnitAddCircle))]

end CircleDomainRigidity

end

end OAI
