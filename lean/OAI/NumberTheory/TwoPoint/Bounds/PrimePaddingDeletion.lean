import OAI.NumberTheory.TwoPoint.Bounds.PrimePaddingFactorization

namespace OAI

/-! The literal tuple-degree deletion keeps the padding weight. Its
expectation factors because the two prime pools are disjoint. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

lemma padding_vertex_square_average (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (site : ℤ) :
    (data.paddingResidueLaw B hB).average (fun z =>
      (actualPaddingVertex data.Q (data.paddingResidueOrigin z + site)) ^ 2) =
        paddingTiltNormalizer data.Q := by
  have he (z : data.Q → Fin B) :
      (actualPaddingVertex data.Q (data.paddingResidueOrigin z + site)) ^ 2 =
        paddingTiltWeight data.Q (paddingResidueAvailable data.Q B site z) := by
    rw [actualPaddingVertex_sq]
    apply actualPaddingWeight_lift
    intro p
    rw [Int.cast_add, data.paddingResidueOrigin_spec]
  simp_rw [he]
  change (FiniteLaw.independent (fun p : data.Q =>
    uniformResidueLaw B p.val (data.primeQ p p.property).pos
      (hB p (mem_union_right _ p.property)))).average
        (fun z => paddingTiltWeight data.Q (paddingResidueAvailable data.Q B site z)) = _
  rw [padding_residue_average data.Q B (fun p hp => (data.primeQ p hp).two_le)
    (fun p hp => hB p (mem_union_right _ hp)) site (paddingTiltWeight data.Q)]
  exact padding_tilt_total data.Q _

lemma positive_prime_padding_square_average
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      positivePrimeWeight S (data.residueOrigin x + site) *
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2) =
      positivePrimeNormalizer S * paddingTiltNormalizer data.Q := by
  have hh := data.positive_prime_padding_average hB S hSP site
    (fun n => (actualPaddingVertex data.Q n) ^ 2)
    (fun n m hnm => congrArg (fun t : ℝ => t ^ 2)
      (actualPaddingVertex_residue_congr data.Q n m hnm))
  rw [data.padding_vertex_square_average hB site] at hh
  exact hh

theorem positive_prime_padding_square_degree_tail
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      (positivePrimeWeight S (data.residueOrigin x + site) *
        if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then 1 else 0) * (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2) ≤
      (positivePrimeNormalizer S * Real.exp (-2 * W * S.card)) *
        paddingTiltNormalizer data.Q := by
  have hh := data.positive_prime_padding_degree_tail hB S hSP W hW hmass site
    (fun n => (actualPaddingVertex data.Q n) ^ 2) (fun n => sq_nonneg _)
    (fun n m hnm => congrArg (fun t : ℝ => t ^ 2)
      (actualPaddingVertex_residue_congr data.Q n m hnm))
  rw [data.padding_vertex_square_average hB site] at hh
  exact hh

theorem centered_tuple_padding_square_average
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (d : ℕ) (hd : Squarefree d) (hdP : d.primeFactors ⊆ data.P)
    (hdJ : d.primeFactors.card = J) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      |centeredTuple d.primeFactors (data.residueOrigin x + site)| *
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2) ≤
      ((2 : ℝ) ^ J / d) * paddingTiltNormalizer data.Q := by
  calc
    _ ≤ (data.residueLaw B hB).average (fun x =>
        positivePrimeWeight d.primeFactors (data.residueOrigin x + site) *
          (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2) := by
      apply FiniteLaw.average_mono
      intro x
      exact mul_le_mul_of_nonneg_right (abs_centeredTuple_le_positivePrimeWeight _ _)
        (sq_nonneg _)
    _ = _ := by
      rw [data.positive_prime_padding_square_average hB d.primeFactors hdP site,
        positivePrimeNormalizer_squarefree d hd, hdJ]

theorem centered_tuple_padding_square_degree_tail
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (d : ℕ) (hd : Squarefree d) (hdP : d.primeFactors ⊆ data.P)
    (hdJ : d.primeFactors.card = J) (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * J) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      (|centeredTuple d.primeFactors (data.residueOrigin x + site)| *
        if 6 * W * J < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then 1 else 0) * (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2) ≤
      (((2 : ℝ) ^ J / d) * Real.exp (-2 * W * J)) *
        paddingTiltNormalizer data.Q := by
  have ht := data.positive_prime_padding_square_degree_tail hB d.primeFactors hdP W hW
    (by simpa only [hdJ] using hmass) site
  rw [positivePrimeNormalizer_squarefree d hd, hdJ] at ht
  apply le_trans _ ht
  apply FiniteLaw.average_mono
  intro x
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right (abs_centeredTuple_le_positivePrimeWeight _ _)
  split_ifs <;> norm_num

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI
