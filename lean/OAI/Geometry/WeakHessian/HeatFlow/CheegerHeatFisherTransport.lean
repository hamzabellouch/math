import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatHopfAction
import OAI.Geometry.WeakHessian.Transport.HopfLaxScaleTime

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
open WeakHessianTransport WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_fisher_transport {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hmass : ∫ x,u x ∂m = 1) (hA : Integrable A m)
    {b : ℝ} (hb : 0 < b)
    (hI : ∀ᵐ t ∂volume.restrict (Icc 0 b), Integrable (fisherDensity (m := m) (cheegerHeat h t u)) m)
    (hIt : IntervalIntegrable (fun t => ∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m) volume 0 b) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (cheegerHeat h b u) ∧ q.map Prod.snd = densityMeasure m u ∧
      (∫⁻ p,(edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal
        (b*(∫ t in 0..b,∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m)) := by
  have hi := integrable_of_integral_eq_one hmass
  let := densityMeasure_probability_of_integrable u hun hi hmass
  let := hcd.cheegerHeat_probability hN hfull hfin o h u hun hmass hb.le
  apply exists_proper_coupling_cost_of_hopf_bound
  intro f hf
  obtain ⟨L,hf⟩ := hf
  let g : X →ᵇ ℝ := (1/b) • f
  have hg : LipschitzWith (‖(1/b)‖₊*L) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((1/b)*f x) ((1/b)*f y) ≤ _
    rw [dist_eq_norm,← mul_sub,norm_mul]
    simpa only [NNReal.coe_mul,coe_nnnorm,dist_eq_norm,mul_assoc] using
      mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (norm_nonneg (1/b))
  have H := hcd.cheegerHeat_hopf_action hN hfull hfin o h hu hun hi hA hg hb hI (hIt.div_const 2)
  have heq (x : X) : b*boundedHopfMap g b x = hopfLax f 1 x := by
    rw [boundedHopfMap_apply_pos g hb]
    exact hopfLax_scale_time f hb x
  rw [integral_densityMeasure m _ (cheegerHeat_nonneg h hb.le u hun),integral_densityMeasure m _ hun]
  calc
    (∫ x,cheegerHeat h b u x*hopfLax f 1 x ∂m)-(∫ x,u x*f x ∂m) =
      b*((∫ x,cheegerHeat h b u x*boundedHopfMap g b x ∂m)-(∫ x,u x*g x ∂m)) := by
        rw [mul_sub,← integral_const_mul,← integral_const_mul]
        congr 1
        · apply integral_congr_ae
          exact ae_of_all _ fun x => by dsimp only; rw [← heq]; ring
        · apply integral_congr_ae
          exact ae_of_all _ fun x => by
            simp only [g,BoundedContinuousFunction.smul_apply,smul_eq_mul]
            field_simp
    _ ≤ b*(∫ t in 0..b,(∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m)/2) :=
      mul_le_mul_of_nonneg_left H hb.le
    _ = _ := by rw [intervalIntegral.integral_div]; ring
end WeakHessian

end
end InlinedFile0

end OAI
