import Mathlib
import OAI.Geometry.WeakHessian.Transport.PlanEnergy

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile57
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma hopf_dual_le_coupling_cost (μ ν : ProbabilityMeasure X)
    {q : Measure (X×X)} (hq : IsCoupling q μ ν) (hqt : QuadraticTransportCost q ≠ ∞)
    (f : X →ᵇ ℝ) :
    (∫ x,hopfLax f 1 x ∂(μ:Measure X))-(∫ x,f x ∂(ν:Measure X)) ≤ (QuadraticTransportCost q).toReal/2 := by
  let Q := boundedHopfMap f 1
  have hqp : IsProbabilityMeasure q := by
    constructor
    have H := congrArg (fun r : Measure X => r univ) hq.1
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using H
  let := hqp
  have he : (Q:X → ℝ) = hopfLax f 1 := funext (boundedHopfMap_apply_pos f (by norm_num))
  have iQ : Integrable (fun p : X×X => Q p.1) q := Integrable.of_bound
    (Q.continuous.comp continuous_fst).aestronglyMeasurable ‖Q‖ (ae_of_all _ fun p => Q.norm_coe_le_norm p.1)
  have iF : Integrable (fun p : X×X => f p.2) q := Integrable.of_bound
    (f.continuous.comp continuous_snd).aestronglyMeasurable ‖f‖ (ae_of_all _ fun p => f.norm_coe_le_norm p.2)
  have H : (∫ p : X×X,Q p.1-f p.2 ∂q) ≤ (∫ p : X×X,dist p.1 p.2^2 ∂q)/2 := by
    apply (integral_mono (iQ.sub iF) ((integrable_squared_distance_of_cost hqt).div_const 2) ?_).trans_eq (integral_div _ _)
    intro p
    rw [he]
    have H := hopfLax_le_objective (fun x => (boundedContinuous_bounds f x).1) (by norm_num : (0:ℝ)<1) p.1 p.2
    simp only [hopfObjective,mul_one] at H
    dsimp only [Pi.sub_apply]
    linarith
  rw [integral_sub iQ iF,← integral_map measurable_fst.aemeasurable Q.continuous.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable,hq.1,hq.2,he] at H
  rw [quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  exact H

lemma exists_optimal_coupling_of_finite (μ ν : ProbabilityMeasure X)
    {p : Measure (X×X)} (hp : IsCoupling p μ ν) (hpt : QuadraticTransportCost p ≠ ∞) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ := by
  let I : ℝ≥0∞ := ⨅ q : Measure (X×X),⨅ _ : IsCoupling q μ ν,QuadraticTransportCost q
  have hI : I ≠ ∞ := ne_top_of_le_ne_top hpt (iInf_le_of_le p (iInf_le _ hp))
  have H (f : X →ᵇ ℝ) : (∫ x,hopfLax f 1 x ∂(μ:Measure X))-(∫ x,f x ∂(ν:Measure X)) ≤ I.toReal/2 := by
    let D := (∫ x,hopfLax f 1 x ∂(μ:Measure X))-(∫ x,f x ∂(ν:Measure X))
    have hd : ENNReal.ofReal (2*D) ≤ I := by
      apply le_iInf; intro q; apply le_iInf; intro hq
      by_cases hqt : QuadraticTransportCost q = ∞
      · rw [hqt]; exact le_top
      · apply (ENNReal.ofReal_le_iff_le_toReal hqt).mpr
        have J := hopf_dual_le_coupling_cost μ ν hq hqt f
        dsimp only [D]; linarith
    have J := ENNReal.toReal_mono hI hd
    have : 2*D ≤ I.toReal := by
      by_cases hD : 0 ≤ 2*D
      · rwa [ENNReal.toReal_ofReal hD] at J
      · exact (le_of_lt (lt_of_not_ge hD)).trans ENNReal.toReal_nonneg
    dsimp only [D] at this
    linarith
  obtain ⟨q,hqp,hq0,hq1,hcost⟩ := exists_proper_coupling_cost_of_hopf_bound
    (μ:Measure X) (ν:Measure X) I.toReal (fun f _ => H f)
  rw [ENNReal.ofReal_toReal hI] at hcost
  exact ⟨q,hqp,⟨⟨hq0,hq1⟩,fun r hr => hcost.trans (iInf_le_of_le r (iInf_le _ hr))⟩,
    ne_top_of_le_ne_top hI hcost⟩
end WeakHessian

end
end InlinedFile57

end OAI
