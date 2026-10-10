import OAI.Combinatorics.BalancedRyser.Incidence.AffineMomentAlgebraLemmas
import OAI.Combinatorics.BalancedRyser.Incidence.StabilitySkewCountLemmas

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem missing_mul_real_gap_le_skew (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) :
    ((projectiveLinePoints ell \ B).card : ℝ) *
      ((Fintype.card F : ℝ) - (B \ projectiveLinePoints ell).card) ≤
      ((skewProjective B).card : ℝ) := by
  by_cases h : (B \ projectiveLinePoints ell).card ≤ Fintype.card F
  · have hc := missing_mul_order_sub_offLine_le_skew B ell
    have hR : ((projectiveLinePoints ell \ B).card : ℝ) *
        ((Fintype.card F - (B \ projectiveLinePoints ell).card : ℕ) : ℝ) ≤
        ((skewProjective B).card : ℝ) := by exact_mod_cast hc
    simpa only [Nat.cast_sub h] using hR
  · have hR : (Fintype.card F : ℝ) ≤ (B \ projectiveLinePoints ell).card := by
      exact_mod_cast (show Fintype.card F ≤ (B \ projectiveLinePoints ell).card by omega)
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (show (0 : ℝ) ≤ ((projectiveLinePoints ell \ B).card : ℝ) by positivity)
      (show (Fintype.card F : ℝ) - (B \ projectiveLinePoints ell).card ≤ 0 by linarith)
    exact hnonpos.trans (Nat.cast_nonneg _)

theorem projective_line_source_refinement (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (d : ℕ) (β : ℝ) (hβ : 0 < β)
    (hmissing : (projectiveLinePoints ell \ B).card ≤ d)
    (hsize : (B.card : ℝ) ≤ (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1) - β)
    (hdegree : (d : ℝ) ^ 2 < 2 * ((skewProjective B).card : ℝ))
    (hskew : ((skewProjective B).card : ℝ) < (2 / 9 : ℝ) * (β + 1) ^ 2) :
    (Fintype.card F : ℝ) - 2 * ((skewProjective B).card : ℝ) /
      ((Fintype.card F : ℝ) + 1) ≤
      ((B.filter (fun P => ProjectiveIncident P ell)).card : ℝ) := by
  have hfilter : B.filter (fun P => ProjectiveIncident P ell) =
      B ∩ projectiveLinePoints ell := by ext P; simp
  rw [hfilter]
  have hpart : (projectiveLinePoints ell \ B).card +
      (B ∩ projectiveLinePoints ell).card = Fintype.card F + 1 := by
    rw [Finset.inter_comm B]
    rw [Finset.card_sdiff_add_card_inter, card_projectiveLinePoints]
  have hB := Finset.card_sdiff_add_card_inter B (projectiveLinePoints ell)
  apply StabilityFinalArithmetic.collinear_lower_bound_of_source_bounds
    (Fintype.card F) (B \ projectiveLinePoints ell).card
    (B ∩ projectiveLinePoints ell).card (projectiveLinePoints ell \ B).card d β
    ((skewProjective B).card : ℝ) (Fintype.card_pos_iff.mpr inferInstance)
    hβ (Nat.cast_nonneg _) hpart hmissing
  · simpa only [hB] using hsize
  · exact hdegree
  · exact hskew
  · exact missing_mul_real_gap_le_skew B ell

end Balanced

end OAI
