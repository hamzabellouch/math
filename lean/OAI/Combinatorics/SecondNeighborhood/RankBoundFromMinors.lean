import OAI.Combinatorics.SecondNeighborhood.GenericRankSelection
import OAI.Combinatorics.SecondNeighborhood.KernelBasisLifts
import OAI.Combinatorics.SecondNeighborhood.CompositeRankBound

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open scoped Matrix

variable {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E]

theorem original_add_auxiliary_card_le_corners
    (r : X → X → Prop) (R C : Finset (X × X))
    (α : Finset (↥(Z r R C) × ↥R)) (β : Finset (↥(Z r R C) × ↥C))
    (hα : Bipartite.IsMaximumMatching (matrixLSupport r R C) α)
    (hβ : Bipartite.IsMaximumMatching (matrixNTransposeSupport r R C) β)
    (left : E → ↥R) (right : E → ↥C)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hleft_disjoint : ∀ e (f : ↥α), left e ≠ f.1.2)
    (hright_disjoint : ∀ e (f : ↥β), right e ≠ f.1.2)
    (hconflict : ∀ e, Conflict r (left e).1 (right e).1) :
    Fintype.card E + α.card + β.card ≤ (Z r R C).card + (H r R C).card := by
  classical
  obtain ⟨v, ha, hb, hmax, hdetL, hdetN, hrankL, hrankN⟩ :=
    exists_pruning_rank_coefficients r R C α β hα hβ
  have hupperL : (matrixL r R C (selectedA r v)).rank ≤ Fintype.card ↥α := by
    simpa only [Fintype.card_coe] using hrankL.le
  have hupperN : ((matrixN r R C (selectedB r v))ᵀ).rank ≤ Fintype.card ↥β := by
    simpa only [Fintype.card_coe] using hrankN.le
  obtain ⟨U, hU, hUcoordinate⟩ := exists_normalized_kernelLifts_of_det_ne_zero
    (matrixL r R C (selectedA r v)) (fun f : ↥α => f.1.1)
    (fun f : ↥α => f.1.2) hdetL hupperL left hleft hleft_disjoint
  obtain ⟨W, hW, hWcoordinate⟩ := exists_normalized_kernelLifts_of_det_ne_zero
    (matrixN r R C (selectedB r v))ᵀ (fun f : ↥β => f.1.1)
    (fun f : ↥β => f.1.2) hdetN hupperN right hright hright_disjoint
  have hbound := card_add_rank_matrixL_add_rank_matrixN_le_card_Z_add_card_H_of_lifts
    r R C (selectedA r v) (selectedB r v) ha hb hmax left right U W
    hU hW (fun e => by simpa using hWcoordinate e e) hUcoordinate hconflict
  have hrankN' : (matrixN r R C (selectedB r v)).rank = β.card := by
    simpa only [Matrix.rank_transpose] using hrankN
  simpa only [hrankL, hrankN'] using hbound

end SeymourSecondNeighborhood.Pruning

end OAI
