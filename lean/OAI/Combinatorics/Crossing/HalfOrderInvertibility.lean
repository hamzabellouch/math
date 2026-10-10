import OAI.Combinatorics.Crossing.TriangleFactorization
import OAI.Combinatorics.Crossing.DetectorRank

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rankDetector_halfOrder_isUnit [LinearOrder ι] (s : ℕ) (node : ι → ℝ)
    (hn : Function.Injective node) (hcard : Fintype.card ι = 2*s+1) :
    IsUnit (rankDetector s node (halfOrderMatrix ι)) := by
  let e : OrderedNode s ≃o ι :=
    (Fintype.orderIsoFinOfCardEq (OrderedNode s) (card_orderedNode s)).symm.trans
      (Fintype.orderIsoFinOfCardEq ι hcard)
  have hunit := rankDetector_ordered_isUnit s (node ∘ e) (hn.comp e.injective)
  have he := rankDetector_equiv s node e.toEquiv (halfOrderMatrix ι)
  change rankDetector s (node ∘ e) ((halfOrderMatrix ι).submatrix e e) =
    rankDetector s node (halfOrderMatrix ι) at he
  rw [halfOrderMatrix_orderIso e] at he
  rwa [he] at hunit

theorem lemma4_2 (s : ℕ) (hs : 0 < s) (node : ι → ℝ) (hn : Function.Injective node)
    (hcard : Fintype.card ι = 2*s+1) :
    (∀ r c : ι → ℝ, rankDetector s node (fun p q => r p+c q) = 0) ∧
    (∀ d : ι → ℝ, rankDetector s node (Matrix.diagonal d) = 0) ∧
    (∀ p q : ι, p ≠ q → (rankDetector s node (Matrix.single p q 1)).rank = 1) ∧
    (∀ order : LinearOrder ι, IsUnit (rankDetector s node (@halfOrderMatrix ι order))) := by
  refine ⟨rankDetector_additive s node hn hcard, rankDetector_diagonal s node, ?_, ?_⟩
  · intro p q hpq
    rw [rankDetector_single, one_smul]
    exact detectorAtom_rank_one s hs node hn hpq
  · intro order
    let := order
    exact rankDetector_halfOrder_isUnit s node hn hcard

end Zarankiewicz

end

end OAI
