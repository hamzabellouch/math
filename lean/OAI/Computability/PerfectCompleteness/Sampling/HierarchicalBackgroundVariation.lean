import OAI.Computability.PerfectCompleteness.Construction.HiddenBucketBias
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAgreementMean

namespace OAI

section

namespace PerfectCompleteness.HierarchicalBackgroundVariation

open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] linearMapFintype

private theorem common_right_variation {A B : Type*} [Fintype A] [Fintype B]
    (P Q : FiniteDistribution A) (ν : FiniteDistribution B) :
    (P.product ν).totalVariation (Q.product ν) = P.totalVariation Q := by
  change (∑ z : A × B,
    |P.weight z.1 * ν.weight z.2 - Q.weight z.1 * ν.weight z.2|) / 2 =
      (∑ a : A, |P.weight a - Q.weight a|) / 2
  rw [Fintype.sum_prod_type]
  simp_rw [← sub_mul, abs_mul, abs_of_nonneg (ν.nonnegative _), ← Finset.mul_sum,
    ν.normalized, mul_one]

private theorem variation_triangle {A : Type*} [Fintype A]
    (P U Q : FiniteDistribution A) :
    P.totalVariation Q ≤ P.totalVariation U + U.totalVariation Q := by
  unfold FiniteDistribution.totalVariation
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => abs_sub_le (P.weight x) (U.weight x) (Q.weight x))
  rw [Finset.sum_add_distrib] at h
  linarith

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

local instance backgroundFintype :
    Fintype (HierarchicalAgreementMean.Background (rows := rows) slots upper) := Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) := Fintype.ofFinite _

theorem reference_background
    (backgroundLaw : FiniteDistribution (HierarchicalAgreementMean.Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    (HierarchicalAgreementMean.referenceLaw slots upper backgroundLaw hrows).pushforward Prod.fst =
      backgroundLaw := by
  unfold HierarchicalAgreementMean.referenceLaw
  rw [FiniteDistribution.pushforward_comp]
  change (backgroundLaw.product (HierarchicalAgreementMean.bucketLaw slots upper hrows)).pushforward
    Prod.fst = backgroundLaw
  exact HiddenBucketBias.product_fst _ _

theorem reference_variation
    (P Q : FiniteDistribution (HierarchicalAgreementMean.Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    (HierarchicalAgreementMean.referenceLaw slots upper P hrows).totalVariation
      (HierarchicalAgreementMean.referenceLaw slots upper Q hrows) ≤ P.totalVariation Q :=
  (DensityVariation.variation_pushforward_le
    (P.product (HierarchicalAgreementMean.bucketLaw slots upper hrows))
    (Q.product (HierarchicalAgreementMean.bucketLaw slots upper hrows))
    (HierarchicalAgreementMean.pairRecord slots upper)).trans_eq
      (common_right_variation P Q (HierarchicalAgreementMean.bucketLaw slots upper hrows))

theorem original_background_variation
    (P : FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots upper))
    (referenceBackground : FiniteDistribution
      (HierarchicalAgreementMean.Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    P.totalVariation
        (HierarchicalAgreementMean.referenceLaw slots upper (P.pushforward Prod.fst) hrows) ≤
      2 * P.totalVariation
        (HierarchicalAgreementMean.referenceLaw slots upper referenceBackground hrows) := by
  have hmarginal := DensityVariation.variation_pushforward_le P
    (HierarchicalAgreementMean.referenceLaw slots upper referenceBackground hrows) Prod.fst
  rw [reference_background] at hmarginal
  have href := reference_variation slots upper (P.pushforward Prod.fst) referenceBackground hrows
  rw [FiniteDistribution.totalVariation_comm] at href
  have htriangle := variation_triangle P
    (HierarchicalAgreementMean.referenceLaw slots upper referenceBackground hrows)
    (HierarchicalAgreementMean.referenceLaw slots upper (P.pushforward Prod.fst) hrows)
  linarith

theorem original_background_le_of_bound
    (P : FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots upper))
    (referenceBackground : FiniteDistribution
      (HierarchicalAgreementMean.Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper)) {error : ℝ}
    (herror : P.totalVariation
      (HierarchicalAgreementMean.referenceLaw slots upper referenceBackground hrows) ≤ error) :
    P.totalVariation
        (HierarchicalAgreementMean.referenceLaw slots upper (P.pushforward Prod.fst) hrows) ≤
      2 * error := by
  have h := original_background_variation slots upper P referenceBackground hrows
  linarith

end
end PerfectCompleteness.HierarchicalBackgroundVariation

end

end OAI
