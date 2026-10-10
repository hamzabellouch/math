import Mathlib
import OAI.Probability.SLE.LowerRestartConditionalAllKappa

namespace OAI

/-! Lower Positivity for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge
 
def segment (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) : Set ℂ := γ '' Icc s t
universe v_lower
 

def SourceLowerMainTarget : Prop :=
  ∀ (Ω : Type v_lower) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ κ : ℝ, 0 < κ → κ < ((8 : ℕ) : ℝ) →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (segment (γ ω) s t)
end SLEExactGauge

namespace SLEExactGauge
theorem sourceLowerMain_proved : SourceLowerMainTarget := by
  intro Ω m P hP κ hκ hκ8 γ hSLE h hh hf
  let : IsProbabilityMeasure P := hP
  exact source_lower_universe hκ hκ8 hSLE h hh hf
end SLEExactGauge
end

 
end
end
end

end OAI
