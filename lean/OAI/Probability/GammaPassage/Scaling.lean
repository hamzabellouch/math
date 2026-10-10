import OAI.Probability.FirstPassage.PassageTime
import OAI.Probability.FirstPassage.TiltPath
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace OAI

namespace GammaFPP
open PlanarFPP MeasureTheory Filter
open scoped Topology

/-- Positive scaling commutes with the infimum over finite paths with nonnegative weights. -/
theorem passageTime_scale (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 < c) (p q : Vertex) :
    passageTime (fun e => c * w e) p q = c * passageTime w p q := by
  have hcw : ∀ e, 0 ≤ c * w e := fun e => mul_nonneg hc.le (hw e)
  apply le_antisymm
  · apply (div_le_iff₀' hc).mp
    apply le_csInf (path_costs_nonempty w p q)
    rintro t ⟨ds, hend, rfl⟩
    apply (div_le_iff₀' hc).mpr
    rw [← PlanarFPP.pathCost_scale]
    exact passageTime_le_cost (fun e => c * w e) hcw p q ds hend
  · apply le_csInf (path_costs_nonempty (fun e => c * w e) p q)
    rintro t ⟨ds, hend, rfl⟩
    rw [PlanarFPP.pathCost_scale]
    exact mul_le_mul_of_nonneg_left (passageTime_le_cost w hw p q ds hend) hc.le

/-- Positive scaling preserves the time-constant norm laws. -/
theorem timeConstantNorm_scale {μ : Plane → ℝ} (hμ : TimeConstantNorm μ)
    (c : ℝ) (hc : 0 < c) : TimeConstantNorm (fun v => c * μ v) where
  nonneg v := mul_nonneg hc.le (hμ.nonneg v)
  zero_iff v := by simp only [mul_eq_zero, hc.ne', false_or, hμ.zero_iff v]
  triangle v w := by
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (hμ.triangle v w) hc.le
  homogeneous a v := by
    rw [hμ.homogeneous]
    ring

/-- Scaling transports the almost-sure real-parameter limit for each fixed real direction. -/
theorem isTimeConstant_scale {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {τ : Edge → Ω → ℝ} {μ : Plane → ℝ}
    (hτ : ∀ᵐ ω ∂P, ∀ e, 0 ≤ τ e ω) (hμ : IsTimeConstant P τ μ)
    (c : ℝ) (hc : 0 < c) :
    IsTimeConstant P (fun e ω => c * τ e ω) (fun v => c * μ v) := by
  intro v
  filter_upwards [hτ, hμ v] with ω hω hlim
  have hmul : Tendsto
      (fun t : ℝ => c * (passageTime (fun e => τ e ω) (0, 0)
        (latticeFloor (t • v)) / t)) atTop (𝓝 (c * μ v)) :=
    tendsto_const_nhds.mul hlim
  convert hmul using 1
  ext t
  rw [passageTime_scale (fun e => τ e ω) hω c hc]
  ring

/-- Scaling a differentiable time constant scales its continuous linear derivative. -/
theorem differentiableAwayFromOrigin_scale {μ : Plane → ℝ}
    (hμ : DifferentiableAwayFromOrigin μ) (c : ℝ) :
    DifferentiableAwayFromOrigin (fun v => c * μ v) := by
  intro v hv
  obtain ⟨ℓ, hℓ⟩ := hμ v hv
  refine ⟨c • ℓ, ?_⟩
  apply HasFDerivAt.of_isLittleOTVS
  have ho := (c • ContinuousLinearMap.id ℝ ℝ).isBigOTVS_comp.trans_isLittleOTVS
    hℓ.isLittleOTVS
  simpa only [Function.comp_def, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, mul_sub] using ho

end GammaFPP

end OAI
