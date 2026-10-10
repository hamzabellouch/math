import Mathlib
import OAI.Geometry.WeakHessian.Transport.HopfLpTransportPairing
import OAI.Geometry.WeakHessian.Transport.DensityMeasure
import OAI.Geometry.WeakHessian.Transport.CouplingCostHopfBound

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

namespace WeakHessianTransport
open WeakHessian WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma density_coupling_bound (h : QuadraticCheegerEnergy m)
    {ρ u A : ℝ → Lp ℝ 2 m} {α c C : ℝ}
    (hα : 0 < α) (hρ : ContinuousOn ρ (Icc 0 1))
    (hpos : ∀ t ∈ Icc 0 1, ∀ᵐ x ∂m, 0 ≤ ρ t x)
    (hmass : ∀ t ∈ Icc 0 1, ∫ x, ρ t x ∂m = 1)
    (hlower : ∀ t ∈ Ico 0 1, ∀ᵐ x ∂m, α ≤ ρ t x)
    (hgen : ∀ t ∈ Ico 0 1, (cheeger_closedQuadraticEnergy h).IsFormGenerator (u t) (A t))
    (hener : ∀ t ∈ Ico 0 1, (cheegerEnergy m (u t : X → ℝ)).toReal ≤ C)
    (hderiv : ∀ t ∈ Ico 0 1, HasDerivWithinAt ρ (c • A t) (Ici t) t) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (ρ 1) ∧
      q.map Prod.snd = densityMeasure m (ρ 0) ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal (2*c^2/α*C) := by
  let hp0 := densityMeasure_probability m (ρ 0) (hpos 0 (by norm_num)) (hmass 0 (by norm_num))
  let hp1 := densityMeasure_probability m (ρ 1) (hpos 1 (by norm_num)) (hmass 1 (by norm_num))
  apply exists_coupling_cost_of_hopf_bound _ _ (2*c^2/α*C)
  intro f hf
  obtain ⟨L,hf⟩ := hf
  let f' : C(X,ℝ) := ⟨f,hf.continuous⟩
  have H := hopfLp_transport_pairing_le m h (f := f') hf (by norm_num : (0:ℝ) ≤ 1)
    hα hρ hlower hgen hener hderiv
  have hq : (fun x => hopfLax f 1 x) = (hopfMap f' 1 : X → ℝ) := by
    funext x
    exact (hopfMap_apply_pos f' (by norm_num) x).symm
  rw [hq, integral_densityMeasure_continuousMap m _ (hpos 1 (by norm_num))]
  change _ - (∫ x, f' x ∂densityMeasure m (ρ 0)) ≤ _
  rw [integral_densityMeasure_continuousMap m _ (hpos 0 (by norm_num))]
  change ⟪hopfLp m f' 1,ρ 1⟫_ℝ - ⟪ContinuousMap.toLp 2 m ℝ f',ρ 0⟫_ℝ ≤ _
  calc
    _ ≤ 1*c^2/α*C := H
    _ = _ := by ring

end WeakHessianTransport

end
end InlinedFile0

end OAI
