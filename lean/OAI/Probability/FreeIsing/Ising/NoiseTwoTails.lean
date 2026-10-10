import OAI.Probability.FreeIsing.Ising.OrientedNoiseSplit
import OAI.Probability.FreeIsing.Ising.PathReversalTransport

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds IsingCopyWeightedCut TreeKoopman

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_noiseEnergy_bound_of_two_tails
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t T : ℝ≥0), t ≤ T →
      ∀ (u w : TreeVertex d), treeAdj u w → ∀ (v : TreeVertex d) (p : ℕ),
      p ≤ v.1.length → ∀ (a ε : ℝ), 0 ≤ a → 0 ≤ ε →
      observationLaw μ
        {x | a < extensionAverage hb t false (v.1.take p) (v.1.length - p) x} ≤
          ENNReal.ofReal ε →
      observationLaw μ
        {x | a < extensionAverage hb t true ((reverseVertex v).1.take (v.1.length - p)) p x} ≤
          ENNReal.ofReal ε →
      IsingCopyResponseRowPaths.noiseEnergy (μ := μ) hb t v ≤
        4 * a * C * (v.1.length : ℝ) *
          (∫ q, cavityLogDifference hb t u w q ^ 2 ∂copies beta μ) +
        4 * edgeLogBound d beta T ^ 2 * (v.1.length : ℝ) ^ 2 * ε := by
  obtain ⟨C, hC, hv⟩ := exists_logSum_prefix_variance_bound hμ hd hb hthreshold
  refine ⟨C, hC, ?_⟩
  intro t T ht u w huw v p hp a ε ha hε htail₁ htail₂
  let S := ∫ q, cavityLogDifference hb t u w q ^ 2 ∂copies beta μ
  let M := edgeLogBound d beta T
  let A := a * (C * (p : ℝ) * S) + ((p : ℝ) ^ 2 * M ^ 2) * ε
  let B := a * (C * ((v.1.length - p : ℕ) : ℝ) * S) +
    (((v.1.length - p : ℕ) : ℝ) ^ 2 * M ^ 2) * ε
  have hprefix (left : Bool) :
      weightedLogEnergy (μ := μ) hb t false v (Finset.range p) left ≤ A := by
    exact (integral_prefix_weight_mul_le_of_tail hμ hb ht left false v hp ha hε htail₁).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hv t u w huw false v p hp) ha) le_rfl)
  have hlen : (reverseVertex v).1.length = v.1.length := List.length_reverse
  have hq : v.1.length - p ≤ (reverseVertex v).1.length := by rw [hlen]; omega
  have htail₂' : observationLaw μ
      {x | a < extensionAverage hb t true ((reverseVertex v).1.take (v.1.length - p))
        ((reverseVertex v).1.length - (v.1.length - p)) x} ≤ ENNReal.ofReal ε := by
    simpa only [hlen, Nat.sub_sub_self hp] using htail₂
  have hsuffix (left : Bool) :
      weightedLogEnergy (μ := μ) hb t false v (Finset.Ico p v.1.length) left ≤ B := by
    unfold weightedLogEnergy
    rw [integral_suffix_sq_mul_attenuation_reverse hμ hb t false v p hp left 2]
    exact (integral_prefix_weight_mul_le_of_tail hμ hb ht left true (reverseVertex v)
      hq ha hε htail₂').trans (add_le_add
        (mul_le_mul_of_nonneg_left (hv t u w huw true (reverseVertex v) _ hq) ha) le_rfl)
  have hsum : (p : ℝ) + ((v.1.length - p : ℕ) : ℝ) = (v.1.length : ℝ) := by
    exact_mod_cast Nat.add_sub_of_le hp
  have hsquares : (p : ℝ) ^ 2 + ((v.1.length - p : ℕ) : ℝ) ^ 2 ≤
      (v.1.length : ℝ) ^ 2 := by
    have hpq : 0 ≤ (p : ℝ) * ((v.1.length - p : ℕ) : ℝ) := by positivity
    nlinarith
  calc
    _ ≤ 2 *
      (weightedLogEnergy (μ := μ) hb t false v (Finset.range p) true +
       weightedLogEnergy (μ := μ) hb t false v (Finset.range p) false +
       weightedLogEnergy (μ := μ) hb t false v (Finset.Ico p v.1.length) true +
       weightedLogEnergy (μ := μ) hb t false v (Finset.Ico p v.1.length) false) :=
      noiseEnergy_le_four_half_weights hμ hb t v hp
    _ ≤ 2 * (A + A + B + B) := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add (hprefix true) (hprefix false))
        (hsuffix true)) (hsuffix false)) (by norm_num)
    _ = 4 * a * C * (v.1.length : ℝ) * S +
        4 * M ^ 2 * ((p : ℝ) ^ 2 + ((v.1.length - p : ℕ) : ℝ) ^ 2) * ε := by
      rw [← hsum]
      dsimp only [A, B]
      ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquares (by positivity)) hε

end Problem367.IsingOrientedPath

end

end OAI
