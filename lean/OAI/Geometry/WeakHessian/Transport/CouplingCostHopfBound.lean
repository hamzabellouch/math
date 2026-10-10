import Mathlib
import OAI.Geometry.WeakHessian.Transport.QuadraticCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace

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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


namespace WeakHessianTransport
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma exists_coupling_cost_of_hopf_bound (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (B : ℝ)
    (hdual : ∀ f : X → ℝ, (∃ L : ℝ≥0, LipschitzWith L f) →
      (∫ x, hopfLax f 1 x ∂μ) - (∫ x, f x ∂ν) ≤ B/2) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal B := by
  obtain ⟨q,hq,hq0,hq1,_,hqlower⟩ := compact_hopf_duality μ ν (by norm_num : (0:ℝ) < 1)
  let := hq
  have hI : (∫ p, quadraticCost 1 p ∂q) ≤ B/2 := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨f,hf,hfcost⟩ := hqlower ε hε
    have hb := hdual f hf
    linarith
  have hcont : Continuous (fun p : X×X => dist p.1 p.2 ^ 2) :=
    (continuous_fst.dist continuous_snd).pow 2
  have hint := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := q)
  have hsq : (∫ p : X×X, dist p.1 p.2^2 ∂q) ≤ B := by
    have heq : (∫ p : X×X, dist p.1 p.2^2 ∂q) = 2*(∫ p, quadraticCost 1 p ∂q) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun p => by simp only [quadraticCost_apply]; ring)
    rw [heq]
    linarith
  refine ⟨q,hq,hq0,hq1,?_⟩
  calc
    (∫⁻ p, (edist p.1 p.2)^2 ∂q) = ∫⁻ p : X×X, ENNReal.ofReal (dist p.1 p.2^2) ∂q := by
      apply lintegral_congr
      intro p
      rw [edist_dist,ENNReal.ofReal_pow dist_nonneg]
    _ = ENNReal.ofReal (∫ p : X×X, dist p.1 p.2^2 ∂q) :=
      (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun p => sq_nonneg (dist p.1 p.2)))).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hsq

end WeakHessianTransport

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

end

end OAI
