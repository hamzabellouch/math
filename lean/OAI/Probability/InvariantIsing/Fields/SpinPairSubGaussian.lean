import OAI.Probability.InvariantIsing.Pressure.EntropyMeanComparison
import OAI.Probability.InvariantIsing.Fields.FieldPairProductLaw

namespace OAI

/-! The independent canonical site-pair law supplies the dimension-sharp
concentration bound needed in constrained magnetic replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def spinPairSiteValue (p : Bool × Bool) : ℝ := spinValue p.1 * spinValue p.2

def spinPairSiteSum {N : ℕ} (u : Fin N → Bool × Bool) : ℝ := ∑ j, spinPairSiteValue (u j)

lemma spinPairSiteValue_bounds (p : Bool × Bool) : spinPairSiteValue p ∈ Set.Icc (-1) 1 := by
  rcases p with ⟨a,b⟩
  cases a <;> cases b <;> norm_num [spinPairSiteValue, spinValue]

lemma spinPairSiteSum_subgaussian {N : ℕ} (ν : Fin N → Measure (Bool × Bool))
    [∀ i, IsProbabilityMeasure (ν i)] :
    HasSubgaussianMGF (fun u => spinPairSiteSum u - ∑ j, ∫ p, spinPairSiteValue p ∂ν j)
      (N : ℝ≥0) (Measure.pi ν) := by
  let X := fun j p => spinPairSiteValue p - ∫ q, spinPairSiteValue q ∂ν j
  have hi := iIndepFun_pi (μ := ν) (X := X)
    (fun _ => (measurable_of_finite _).aemeasurable)
  have hg (j : Fin N) : HasSubgaussianMGF (fun u : Fin N → Bool × Bool => X j (u j)) 1
      (Measure.pi ν) := by
    apply HasSubgaussianMGF.of_map (X := X j) (μ := Measure.pi ν) (c := 1)
      (measurePreserving_eval ν j).measurable.aemeasurable
    rw [(measurePreserving_eval ν j).map_eq]
    have hs := hasSubgaussianMGF_of_mem_Icc (μ := ν j) (X := spinPairSiteValue)
      (measurable_of_finite _).aemeasurable (Filter.Eventually.of_forall spinPairSiteValue_bounds)
    norm_num at hs
    exact hs
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (c := fun _ => 1)
    (fun j _ => hg j)
  simpa only [X, spinPairSiteSum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_one] using hs

lemma spinPairSiteSum_entropy_bound {N : ℕ} (μ : Measure (Fin N → Bool × Bool))
    [IsProbabilityMeasure μ] (ν : Fin N → Measure (Bool × Bool))
    [∀ i, IsProbabilityMeasure (ν i)] (hK : klDiv μ (Measure.pi ν) ≠ ⊤)
    {t : ℝ} (ht : 0 < t) :
    |(∫ u, spinPairSiteSum u ∂μ) - ∑ j, ∫ p, spinPairSiteValue p ∂ν j| ≤
      (klDiv μ (Measure.pi ν)).toReal / t + N * t / 2 := by
  have hk := klDiv_ne_top_iff.mp hK
  have he := entropy_subgaussian_mean μ (Measure.pi ν) hk.1 hk.2
    (fun u => spinPairSiteSum u - ∑ j, ∫ p, spinPairSiteValue p ∂ν j)
    Integrable.of_finite (spinPairSiteSum_subgaussian ν) ht
  simpa only [integral_sub Integrable.of_finite (integrable_const _), integral_const,
    measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, NNReal.coe_natCast] using he

end InvariantIsing

end

end OAI
