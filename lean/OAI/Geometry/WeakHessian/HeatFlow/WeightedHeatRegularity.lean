import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.WeightedEnergySpace
import OAI.Geometry.WeakHessian.LocalBounds.EnergyIdentification
import OAI.Geometry.WeakHessian.LocalBounds.DriftQuantitative

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile184
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma RCD.weighted_formGenerator_iff {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u A : Lp ℝ 2 (exponentialMeasure m V)) :
    IsLaplacian (exponentialMeasure m V) (u : X → ℝ) A ↔
      (cheeger_closedQuadraticEnergy h).IsFormGenerator u A := by
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal)
    (exponentialMeasure_comparable (m := m) hBV).2
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hBV (f := f) hf
  exact ⟨identified_formGenerator_of_isLaplacian hnfin hID h u A,
    identified_isLaplacian_of_formGenerator hnfin hID h u A⟩

lemma RCD.weighted_heat_uniform_lipschitz {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    {u A : Lp ℝ 2 (exponentialMeasure m V)}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {Bu BA : ℝ} (hBu : 0 ≤ Bu) (hBA : 0 ≤ BA)
    (hub : ∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ Bu)
    (hAb : ∀ᵐ x ∂exponentialMeasure m V,|A x| ≤ BA) :
    ∃ M : ℝ≥0,∀ t : ℝ,0 ≤ t → ∃ g : X → ℝ,LipschitzWith M g ∧
      g =ᵐ[exponentialMeasure m V] cheegerHeat h t u := by
  obtain ⟨τ,hτ,hL2,hLinf⟩ := positive_small_drift_time K L
  refine ⟨Real.toNNReal (5*(2*(τ⁻¹*|Bu|+|BA|))*Real.exp (|K| *τ)*Real.sqrt τ),?_⟩
  intro t ht
  have hLap := (hrcd.weighted_formGenerator_iff hfin o hBV h _ _).mpr
    ((cheeger_closedQuadraticEnergy h).formGenerator_heat (exponentialMeasure m V) hu t)
  exact hrcd.bounded_weighted_laplacian_lipschitz_quantitative hN hfull hfin o hV hBV
    hτ hL2 hLinf hLap (cheegerHeat_bounded h ht hBu u hub) (cheegerHeat_bounded h ht hBA A hAb)
end WeakHessian

end
end InlinedFile184

end OAI
