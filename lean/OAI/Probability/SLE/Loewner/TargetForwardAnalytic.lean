import OAI.Probability.SLE.Loewner.TargetInverseProperties
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace OAI

/-! Spatial analyticity of the raw forward map follows from the analytic
inverse and its nonzero derivative. -/
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge.Target

lemma differentiableOn_flow_of_inverse
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (T : ℝ≥0)
    (hF : DifferentiableOn ℂ (inverseFlow κ b T) upperHalfPlane)
    (hF' : ∀ w ∈ upperHalfPlane, deriv (inverseFlow κ b T) w ≠ 0) :
    DifferentiableOn ℂ (fun z => flow κ b z T) {z | Surviving κ b z T} := by
  intro z hz
  let w := flow κ b z T
  have hw : w ∈ upperHalfPlane := surviving_flow_mem_upperHalfPlane κ b z T T.coe_nonneg hz
  have han := hF.analyticAt (isOpen_upperHalfPlane.mem_nhds hw)
  have hinv : inverseFlow κ b T w=z := inverseFlow_eq_of_surviving κ b T T.coe_nonneg z w hz rfl
  have hlocal : ∀ᶠ v in 𝓝 w, flow κ b (inverseFlow κ b T v) T=v := by
    filter_upwards [isOpen_upperHalfPlane.mem_nhds hw] with v hv
    exact flow_inverseFlow κ hκ b T v hv
  have hg := han.hasStrictDerivAt.to_local_left_inverse
    (g := fun z => flow κ b z T) (hF' w hw) hlocal
  rw [hinv] at hg
  exact hg.hasDerivAt.differentiableAt.differentiableWithinAt

end SLEExactGauge.Target

end

end OAI
