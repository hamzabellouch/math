import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverDegree

namespace OAI

/-! Real integrals over the actual finite cover are sums of the
sheet integrals over the original fundamental domain. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

local instance primeSheetIntegral_fintype {p : Eisenstein} (hp : primaryPrime p) :
    Fintype (cubicThetaPrimeTransversal hp) := Fintype.ofFinite _

theorem cubicThetaPrimeSheetIntegral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f (cubicThetaPrimeCoverDomain hp) cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCoverDomain hp, f x ∂cubicThetaPointMeasure)=
      ∑ t : cubicThetaPrimeTransversal hp,
        ∫ x in cubicThetaFundamentalDomain, f (t.val • x) ∂cubicThetaPointMeasure := by
  have hmeas (t : cubicThetaPrimeTransversal hp) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) :=
    (measurableEmbedding_const_smul t.val).measurableSet_image' cubicThetaFundamentalDomain_measurable
  have hdis : Pairwise (fun t u : cubicThetaPrimeTransversal hp =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        ((fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain)) := by
    intro t u htu
    exact cubicThetaFundamentalDomain_translates_disjoint (fun h => htu (Subtype.ext h))
  have hint (t : cubicThetaPrimeTransversal hp) :
      IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        cubicThetaPointMeasure :=
    hf.mono_set (subset_iUnion (fun u : cubicThetaPrimeTransversal hp =>
      (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  change (∫ x in ⋃ t : cubicThetaPrimeTransversal hp,
    (fun y : CubicThetaPoint => t.val • y) '' cubicThetaFundamentalDomain, f x
      ∂cubicThetaPointMeasure)=_
  rw [integral_iUnion_fintype hmeas hdis hint]
  apply Finset.sum_congr rfl
  intro t _
  exact (measurePreserving_smul t.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul t.val) f cubicThetaFundamentalDomain

end CubicFirstMoment

end

end OAI
