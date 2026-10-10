import Mathlib
import OAI.Probability.Perceptron.Variational.RoundedMarkedReference
import OAI.Probability.Perceptron.Variational.LabelProfileSingleReference

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem quantile_single_reference_exists (q : Time→Time) (hq : Monotone q)
    (g : Jet3) (v : ℝ→ᵇℝ) : ∃ c : ℝ, |c|≤‖v‖ ∧ ∀ b : Bool,
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f v (secondPairMark v b)))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j
        ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v (secondPairMark v b)))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationSingleMoment g.f v (secondPairMark v b) j
          (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 1 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v (secondPairMark v b)))))=
          c^(pairMarkPower b) := by
  let a : ℕ→ℝ := fun n => roundedSingleCoeff (unitQuantileField q hq) n g v
  have hb (n : ℕ) : a n∈Icc (-‖v‖) ‖v‖ := abs_le.mp (roundedSingleCoeff_bound _ _ _ _)
  obtain ⟨c,hc,s,hs,ht⟩ := isCompact_Icc.isSeqCompact hb
  change Tendsto (fun n => roundedSingleCoeff (unitQuantileField q hq) (s n) g v) atTop (𝓝 c) at ht
  refine ⟨c,abs_le.mpr hc,fun b => ?_⟩
  apply rounded_single_reference_exists q hq g v (secondPairMark v b) s hs
  cases b
  · simpa only [a,Function.comp_apply,secondPairMark,pairMarkPower,Bool.false_eq_true,ite_false,roundedSingleCoeff_one,
      pow_one,mul_one] using ht
  · simpa only [a,Function.comp_apply,secondPairMark,pairMarkPower,ite_true,pow_two] using ht.mul ht

end SphericalPerceptronFreeEnergy
end

end OAI
