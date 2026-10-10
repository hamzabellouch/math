import OAI.Analysis.Pureness.Stabilization.Truncation
import OAI.Analysis.Pureness.Stabilization.RankBounds

namespace OAI
noncomputable section
open scoped NNReal Topology
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma abs_mul_left_cuntzBelow (b x : A) : CuntzBelow (Positive.abs (b*x)) (Positive.abs x) := by
  have h := CStarAlgebra.star_left_conjugate_le_norm_smul
    (a := x) (b := star b*b) (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg b))
  have ho : (Positive.starMul (b*x)).1 ≤ ‖star b*b‖ • (Positive.starMul x).1 := by
    change star (b*x)*(b*x) ≤ ‖star b*b‖ • (star x*x)
    rw [star_mul]
    convert h using 1
    noncomm_ring
  exact (abs_cuntzBelow_starMul (b*x)).trans
    ((CuntzBelow.of_le_smul _ _ ‖star b*b‖ (norm_nonneg _) ho).trans (starMul_cuntzBelow_abs x))

lemma abs_star_cuntzBelow (x : A) : CuntzBelow (Positive.abs (star x)) (Positive.abs x) := by
  have h : CuntzBelow (Positive.starMul (star x)) (Positive.starMul x) := by
    simpa only [Positive.starMul, Positive.mulStar, star_star] using mulStar_cuntzBelow_starMul x
  exact (abs_cuntzBelow_starMul (star x)).trans (h.trans (starMul_cuntzBelow_abs x))

lemma abs_mul_right_cuntzBelow (b x : A) : CuntzBelow (Positive.abs (x*b)) (Positive.abs x) := by
  have h := abs_star_cuntzBelow (star (x*b))
  rw [star_star, star_mul] at h
  exact h.trans ((abs_mul_left_cuntzBelow (star b) (star x)).trans (abs_star_cuntzBelow x))

theorem product_cut_comparisons (b x : A) (ε : ℝ≥0) (hε : 0 < ε)
    (M : ℝ≥0) (hM : 0 < M) (hb : ‖b‖ ≤ M) :
    CuntzBelow (Positive.cut ε (Positive.abs (b*x)))
      (Positive.cut (ε/(2*M)) (Positive.abs x)) ∧
    CuntzBelow (Positive.cut ε (Positive.abs (x*b)))
      (Positive.cut (ε/(2*M)) (Positive.abs x)) := by
  let δ := ε/(2*M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨z, hz, haz⟩ := exists_cut_truncation x δ hδ
  have hbound : (M : ℝ)*(δ : ℝ) < ε := by
    dsimp [δ]
    have he : (M : ℝ)*(ε / (2*M) : ℝ) = (ε : ℝ)/2 := by field_simp
    rw [he]
    exact half_lt_self hε
  have hl : ‖b*x-b*z‖ < ε := by
    rw [← mul_sub]
    exact (norm_mul_le _ _).trans_lt ((mul_le_mul hb hz (norm_nonneg _) M.2).trans_lt hbound)
  have hr : ‖x*b-z*b‖ < ε := by
    rw [← sub_mul]
    exact (norm_mul_le _ _).trans_lt ((mul_le_mul hz hb (norm_nonneg _) δ.2).trans_lt
      (by simpa only [mul_comm] using hbound))
  constructor
  · simpa only [haz] using (abs_cut_cuntzBelow_of_norm_sub_lt (b*x) (b*z) ε hε hl).trans
      (abs_mul_left_cuntzBelow b z)
  · simpa only [haz] using (abs_cut_cuntzBelow_of_norm_sub_lt (x*b) (z*b) ε hε hr).trans
      (abs_mul_right_cuntzBelow b z)

theorem perturbation_cut_comparison (x y : A) (ε : ℝ≥0) (hε : 0 < ε)
    (hxy : ‖x-y‖ < (ε : ℝ)/4) :
    CuntzBelow (Positive.cut ε (Positive.abs x)) (Positive.cut (ε/2) (Positive.abs y)) := by
  obtain ⟨z, hz, haz⟩ := exists_cut_truncation y (ε/2) (by positivity)
  have h : ‖x-z‖ < ε := by
    have ht : ‖x-z‖ ≤ ‖x-y‖ + ‖y-z‖ := by
      calc
        _ = ‖(x-y)+(y-z)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hz' : ‖y-z‖ ≤ (ε : ℝ)/2 := by exact_mod_cast hz
    linarith [show (0 : ℝ) < ε from hε]
  simpa only [haz] using abs_cut_cuntzBelow_of_norm_sub_lt x z ε hε h

theorem product_cut_ranks (τ : ExtendedTrace A) (b x : A) (ε : ℝ≥0) (hε : 0 < ε)
    (M : ℝ≥0) (hM : 0 < M) (hb : ‖b‖ ≤ M) :
    τ.rank (Positive.cut ε (Positive.abs (b*x))) ≤ τ.rank (Positive.cut (ε/(2*M)) (Positive.abs x)) ∧
    τ.rank (Positive.cut ε (Positive.abs (x*b))) ≤ τ.rank (Positive.cut (ε/(2*M)) (Positive.abs x)) := by
  obtain ⟨hl, hr⟩ := product_cut_comparisons b x ε hε M hM hb
  exact ⟨τ.rank_le_of_cuntzBelow hl, τ.rank_le_of_cuntzBelow hr⟩

theorem adjoint_cut_comparison (x : A) (ε : ℝ≥0) (hε : 0 < ε) :
    CuntzBelow (Positive.cut ε (Positive.abs (star x))) (Positive.cut ε (Positive.abs x)) := by
  obtain ⟨z, hz, haz⟩ := exists_cut_truncation x ε hε
  apply CuntzBelow.of_cuts
  intro δ hδ
  rw [Positive.cut_cut, add_comm ε δ]
  have hn : ‖star x-star z‖ < ((δ+ε : ℝ≥0) : ℝ) := by
    rw [← star_sub, norm_star]
    exact hz.trans_lt (by exact_mod_cast lt_add_of_pos_left ε hδ)
  have h := (abs_cut_cuntzBelow_of_norm_sub_lt (star x) (star z) (δ+ε) (by positivity) hn).trans
    (abs_star_cuntzBelow z)
  simpa only [haz] using h

theorem adjoint_cut_ranks (τ : ExtendedTrace A) (x : A) (ε : ℝ≥0) (hε : 0 < ε) :
    τ.rank (Positive.cut ε (Positive.abs (star x))) = τ.rank (Positive.cut ε (Positive.abs x)) := by
  apply τ.rank_eq_of_cuntzEquivalent (adjoint_cut_comparison x ε hε)
  simpa only [star_star] using adjoint_cut_comparison (star x) ε hε
end CuntzTrace

end

end OAI
