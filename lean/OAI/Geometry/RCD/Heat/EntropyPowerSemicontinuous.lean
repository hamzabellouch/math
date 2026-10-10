import OAI.Geometry.RCD.Transport.BoundedEntropySemicontinuous

namespace OAI

/-! # Upper semicontinuity of entropy power for the bounded transport law -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem bounded_entropy_power_upperSemicontinuous (μ : Measure X) [SigmaFinite μ]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hs : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B)
    {N : ℝ} (hN : 0 < N) :
    UpperSemicontinuous (fun t : Time => Real.exp (-(boltzmannEntropy μ (π.map (fun γ => γ t)))/N)) := by
  have hcont : Continuous (fun a : ℝ => Real.exp (-a/N)) := by fun_prop
  have hanti : Antitone (fun a : ℝ => Real.exp (-a/N)) := by
    intro a b hab
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hab) hN.le)
  exact hcont.comp_lowerSemicontinuous_antitone
    (bounded_entropy_lowerSemicontinuous μ hB π hC hc hs) hanti

end RegularPointCoordinates

end

end OAI
