import OAI.Analysis.Pureness.Stabilization.Perturbation
import OAI.Analysis.Pureness.Stabilization.RankBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal
variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem exists_cut_cuntzBelow_cut {a b : Positive D} (hab : CuntzTrace.CuntzBelow a b)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ CuntzTrace.CuntzBelow (Positive.cut ε a) (Positive.cut δ b) := by
  obtain ⟨v,hv⟩ := hab ((ε : ℝ)/2) (by exact half_pos hε)
  let q : ℝ := ‖v‖^2
  have hq : 0 ≤ q := sq_nonneg _
  let δ : ℝ≥0 := ⟨(ε : ℝ)/(2*(q+1)), (div_pos (show (0 : ℝ) < ε from hε) (by positivity)).le⟩
  have hδ : 0 < δ := div_pos (show (0 : ℝ) < ε from hε) (by positivity)
  have he : (δ : ℝ)*(2*(q+1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hsmall : q*(δ : ℝ) < (ε : ℝ)/2 := by
    have hd : (0 : ℝ) < δ := hδ
    nlinarith
  let c : Positive D := ⟨star v * (Positive.cut δ b).1 * v,
    star_left_conjugate_nonneg (Positive.cut δ b).2 v⟩
  have hn : ‖a.1-c.1‖ < ε := by
    have hdiff : ‖star v*b.1*v-c.1‖ ≤ q*(δ : ℝ) := by
      calc
        _ = ‖star v*(b.1-(Positive.cut δ b).1)*v‖ := by congr 1; dsimp [c]; noncomm_ring
        _ ≤ q*‖b.1-(Positive.cut δ b).1‖ := conjugate_norm_le _ _
        _ ≤ q*(δ : ℝ) := mul_le_mul_of_nonneg_left (Positive.norm_sub_cut_le δ b) hq
    have ht : ‖a.1-c.1‖ ≤ ‖a.1-star v*b.1*v‖ + ‖star v*b.1*v-c.1‖ := by
      calc
        _ = ‖(a.1-star v*b.1*v)+(star v*b.1*v-c.1)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hv' := hv
    rw [norm_sub_rev] at hv'
    linarith
  exact ⟨δ,hδ,(cut_cuntzBelow_of_norm_sub_lt a c ε hε hn).trans
    (conjugate_cuntzBelow (Positive.cut δ b) v)⟩

theorem cut_cuntzBelow_cut_of_dist {a b : Positive D} (ε : ℝ≥0) (hε : 0 < ε)
    (h : dist a b < (ε : ℝ)/2) :
    CuntzTrace.CuntzBelow (Positive.cut ε a) (Positive.cut (ε/2) b) := by
  apply cut_cuntzBelow_of_norm_sub_lt _ _ ε hε
  have ht : ‖a.1-(Positive.cut (ε/2) b).1‖ ≤
      ‖a.1-b.1‖+‖b.1-(Positive.cut (ε/2) b).1‖ := by
    calc
      _ = ‖(a.1-b.1)+(b.1-(Positive.cut (ε/2) b).1)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hb : ‖b.1-(Positive.cut (ε/2) b).1‖ ≤ (ε : ℝ)/2 := Positive.norm_sub_cut_le (ε/2) b
  have hab : ‖a.1-b.1‖ < (ε : ℝ)/2 := by simpa only [Subtype.dist_eq, dist_eq_norm] using h
  linarith

lemma positive_cut_antitone (a : Positive D) : Antitone (fun ε : ℝ≥0 => Positive.cut ε a) := by
  intro ε δ h
  change cfcₙ (fun t : ℝ => max (t-δ) 0) a.1 ≤ cfcₙ (fun t : ℝ => max (t-ε) 0) a.1
  apply (cfcₙ_le_iff _ _ a.1 (hf0 := by simp) (hg0 := by simp)
    (ha := IsSelfAdjoint.of_nonneg a.2)).mpr
  intro t _
  exact max_le_max (sub_le_sub_left (show (ε : ℝ) ≤ δ from h) t) le_rfl
end CuntzPureness

end

end OAI
