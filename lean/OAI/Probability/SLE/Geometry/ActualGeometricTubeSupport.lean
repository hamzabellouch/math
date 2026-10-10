import OAI.Probability.SLE.Loewner.SlitRawCapacity
import OAI.Probability.SLE.Loewner.SlitRealCharacteristics
import OAI.Probability.SLE.Geometry.GeometricTubeSupport

namespace OAI

/-! The required open-tube support follows from the actual capacity
driver of a prescribed simple arc, finite Brownian driver tubes, and
deterministic trace stability. No geometric support input is assumed. -/
noncomputable section
open Set Filter Function Complex _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge

theorem ordinary_geometricTubeSupport
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0<κ) (γ : Ω → ℝ≥0 → ℂ)
    (hSLE : IsOrdinaryChordalSLE κ γ P) : PublishedGeometricTubeSupport P γ := by
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  intro z p hi hH N V hN hV hpN hzV
  let c := p.toContinuousMap
  have hc0 : c 0=0 := p.source
  have hcH : ∀ t : unitInterval, t≠0 → c t∈upperHalfPlane := hH
  have hcl : (1:unitInterval)∈closure (Ioo (0:unitInterval) 1) := by
    rw [closure_Ioo (by norm_num : (0:unitInterval)≠1)]
    simp
  have hnear : c ⁻¹' V∈𝓝 (1:unitInterval) := c.continuous.continuousAt.preimage_mem_nhds
    (hV.mem_nhds (by change p 1∈V; rw [p.target]; exact hzV))
  obtain ⟨T,hTV,hT0,hT⟩ := mem_closure_iff_nhds.mp hcl (c ⁻¹' V) hnear
  let A := slitCapacityHorizon c hi hc0 hcH T
  let b := slitCapacityDriver c hi hc0 hcH hT
  let β := fun t : ℝ≥0 => Target.trace 1 b t
  have hA : 0<A := div_pos (initialCapacity_pos c hi hc0 hcH (ne_of_gt hT0)) (by norm_num)
  have hβA : β A=c T := by
    change Target.trace 1 (slitCapacityDriver c hi hc0 hcH hT)
      (slitCapacityHorizon c hi hc0 hcH T)=c T
    rw [slitCapacity_raw_trace_eq c hi hc0 hcH hT le_rfl]
    change c (slitCapacityTime c hi hc0 hcH T A)=c T
    rw [slitCapacityTime_after c hi hc0 hcH T le_rfl]
  have hsub : β '' Icc 0 A ⊆ N := by
    change (fun t : ℝ≥0 => Target.trace 1 (slitCapacityDriver c hi hc0 hcH hT) t) '' Icc 0 A ⊆ N
    rw [slitCapacity_raw_initial_range c hi hc0 hcH hT le_rfl,
      slitCapacityCurve_initial_range c hi hc0 hcH T le_rfl,
      slitCapacityTime_after c hi hc0 hcH T le_rfl]
    exact (initialSubarc_range_subset c T).trans hpN
  have hfree := (a.slitCapacity_raw_geometry hκ c hi hc0 hcH hT0 hT).2.2.2.2 A hA
  exact ordinary_regular_slit_tube_positive P κ hκ γ hSLE b.toContinuousMap (map_zero b)
    (a.slit_raw_capacity_witness hκ c hi hc0 hcH hT0 hT) A hA hfree
    (slit_regularRealCharacteristics c hi hc0 hcH hT)
    (by change 0<(β A).im; rw [hβA]; exact hcH T (ne_of_gt hT0))
    N V hN hV hsub (by change β A∈V; rw [hβA]; exact hTV)

end SLEExactGauge

end

end OAI
