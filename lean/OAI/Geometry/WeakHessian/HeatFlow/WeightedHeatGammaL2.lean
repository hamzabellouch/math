import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatRegularity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile200
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.weighted_heat_gamma_memLp {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    {u A : Lp ℝ 2 (exponentialMeasure m V)}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {Bu BA : ℝ} (hBu : 0 ≤ Bu) (hBA : 0 ≤ BA)
    (hub : ∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ Bu)
    (hAb : ∀ᵐ x ∂exponentialMeasure m V,|A x| ≤ BA) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (gamma (exponentialMeasure m V) (cheegerHeat h t u) (cheegerHeat h t u)) 2
      (exponentialMeasure m V) := by
  let ν := exponentialMeasure m V
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hgen := (hrcd.weighted_formGenerator_iff hfin o hBV h _ _).mpr
    ((cheeger_closedQuadraticEnergy h).formGenerator_heat ν hu t)
  obtain ⟨M,hM⟩ := hrcd.weighted_heat_uniform_lipschitz hN hfull hfin o hV hBV h hu hBu hBA hub hAb
  obtain ⟨g,hg,hge⟩ := hM t ht
  have hgSob := (hgen.congr_ae hge.symm .rfl).1
  exact (memLp_congr_ae (gamma_congr_ae hge hge)).mp
    (memLp_gamma_of_lipschitz hnfin hnpar hg hgSob)
end WeakHessian

end
end InlinedFile200

end OAI
