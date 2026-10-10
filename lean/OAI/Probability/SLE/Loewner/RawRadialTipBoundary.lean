import OAI.Probability.SLE.Loewner.RawSurvivingAnalytic

namespace OAI

/-! A radial inverse limit lies outside the open raw survival domain.
This uses only the stated limit, with no regularity of the driver beyond
its defining continuity. -/
noncomputable section
open Set Filter Complex _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge

theorem RegularSLEPresentation.raw_radial_tip_not_surviving
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (hκ : 0<κ)
    (b : Target.Driver) (T : ℝ≥0) (z : ℂ)
    (hl : Tendsto (fun y : ℝ => Target.inverseFlow 1 b T ((b T:ℂ)+(y:ℂ)*I))
      (𝓝[>] 0) (𝓝 z)) : ¬Target.Surviving 1 b z T := by
  intro hs
  have hc := ((a.raw_forward_holomorphic hκ b T).differentiableAt
    ((a.raw_surviving_isOpen hκ b T).mem_nhds hs)).continuousAt
  have ht := hc.tendsto.comp hl
  have he : (fun y : ℝ => Target.flow 1 b
      (Target.inverseFlow 1 b T ((b T:ℂ)+(y:ℂ)*I)) T)
      =ᶠ[𝓝[>] (0:ℝ)] (fun y => (b T:ℂ)+(y:ℂ)*I) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact Target.flow_inverseFlow 1 (by norm_num) b T _
      (by simpa [upperHalfPlane] using hy)
  have hv : Tendsto (fun y : ℝ => (b T:ℂ)+(y:ℂ)*I)
      (𝓝[>] 0) (𝓝 (b T:ℂ)) := by
    have h : Continuous (fun y : ℝ => (b T:ℂ)+(y:ℂ)*I) := by fun_prop
    simpa only [ofReal_zero,zero_mul,add_zero] using
      (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hval := tendsto_nhds_unique ht (hv.congr' he.symm)
  have hp := Target.surviving_flow_mem_upperHalfPlane 1 b z T T.coe_nonneg hs
  rw [hval] at hp
  simp [upperHalfPlane] at hp

end SLEExactGauge

end

end OAI
