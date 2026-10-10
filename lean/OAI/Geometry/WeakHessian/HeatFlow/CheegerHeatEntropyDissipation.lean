import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatFisherFinite
import OAI.Geometry.WeakHessian.Entropy.ReducedEntropy

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology InnerProductSpace NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_entropy_dissipation {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    {b : ℝ} (hb : 0 ≤ b) :
    (∫ t in 0..b,∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m) =
      (∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m) := by
  have ht : ∀ᵐ t ∂volume.restrict (Icc 0 b),t ∈ Icc 0 b := ae_restrict_mem measurableSet_Icc
  have hL (t : ℝ) := hcd.global_isLaplacian_of_formGenerator hfin o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  have hI := hcd.cheegerHeat_fisher_finite_action hN hfull hfin o h hu hun hi hV hU hD hw hb
  have hFI := integral_regularizedFisher_action_tendsto (u := fun t => cheegerHeat h t u)
    (g := fun t => weakGradient m (cheegerHeat h t u)) (ν := volume.restrict (Icc 0 b))
    (ae_of_all _ fun t => Lp.aestronglyMeasurable _)
    (ht.mono fun t ht => cheegerHeat_nonneg h ht.1 u hun)
    (ae_of_all _ fun t => (hL t).1.2.2)
    (ae_of_all _ fun t => weakGradient_zero_on_zero (hL t).1.2.1 (Lp.stronglyMeasurable _).measurable)
    (fun n => ((hcd.cheegerHeat_regularizedFisher_continuousOn hfin o h hu hun
      (fisherEpsilon_pos n)).mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc)
    hI.1 ((intervalIntegrable_iff_integrableOn_Icc_of_le hb).mp hI.2.1)
  have hUt := (hcd.cheegerHeat_weighted hfin o h u hV hU hb).1
  have he0 := tendsto_integral_renormalizedEntropy (Lp.memLp u) hun (weighted_pairing hU hD).1 hw
  have het := tendsto_integral_renormalizedEntropy (Lp.memLp (cheegerHeat h b u))
    (cheegerHeat_nonneg h hb u hun) (weighted_pairing hUt hD).1 hw
  have heq (n : ℕ) :
      (∫ t in Icc 0 b,∫ x,(weakGradient m (cheegerHeat h t u) x)^2/(cheegerHeat h t u x+fisherEpsilon n) ∂m) =
        (∫ x,renormalizedEntropy (fisherEpsilon n) (u x) ∂m)-
        (∫ x,renormalizedEntropy (fisherEpsilon n) (cheegerHeat h b u x) ∂m) := by
    have H := hcd.cheegerHeat_renormalizedEntropy_FTC hN hfull hfin o h hu hun hi (fisherEpsilon_pos n) hb
    rwa [intervalIntegral.integral_of_le hb,← integral_Icc_eq_integral_Ioc] at H
  have he : (∫ t in Icc 0 b,∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m) =
      (∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m) :=
    tendsto_nhds_unique (hFI.congr heq) (he0.sub het)
  rwa [intervalIntegral.integral_of_le hb,← integral_Icc_eq_integral_Ioc]

lemma CurvatureDimension.cheegerHeat_entropy_transport {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hmass : ∫ x,u x ∂m = 1) (hA : Integrable A m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    {b : ℝ} (hb : 0 < b) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (cheegerHeat h b u) ∧ q.map Prod.snd = densityMeasure m u ∧
      (∫⁻ p,(edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal
        (b*((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m))) := by
  have H := hcd.cheegerHeat_weighted_transport hN hfull hfin o h hu hun hmass hA hV hU hD hw hb
  rwa [hcd.cheegerHeat_entropy_dissipation hN hfull hfin o h hu hun
    (integrable_of_integral_eq_one hmass) hV hU hD hw hb.le] at H
end WeakHessian

end
end InlinedFile0

end OAI
