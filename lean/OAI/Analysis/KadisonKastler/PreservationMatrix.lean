import OAI.Analysis.KadisonKastler.IncidenceMatrices
import OAI.Analysis.KadisonKastler.ProjectionMatrices
import OAI.Analysis.KadisonKastler.ScalarAmplification

namespace OAI

/-! # The subset matrix at a preservation cut -/

namespace KadisonKastler

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α]

theorem missing_word_label_exists (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (A : WordSubset W q) (B : WordSubset W p)
    (hAB : Disjoint A.val B.val) : ∃ a, W \ (A.val ∪ B.val) = {a} := by
  apply card_eq_one.mp
  rw [card_sdiff_of_subset (union_subset A.property.1 B.property.1),
    card_union_of_disjoint hAB, A.property.2, B.property.2, hW]
  omega

def missingWordLabel (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (A : WordSubset W q) (B : WordSubset W p)
    (hAB : Disjoint A.val B.val) : α :=
  Classical.choose (missing_word_label_exists W hW A B hAB)

theorem missingWordLabel_spec (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (A : WordSubset W q) (B : WordSubset W p)
    (hAB : Disjoint A.val B.val) :
    W \ (A.val ∪ B.val) = {missingWordLabel W hW A B hAB} :=
  Classical.choose_spec (missing_word_label_exists W hW A B hAB)

theorem missingWordLabel_right_injective (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (A : WordSubset W q) (B C : WordSubset W p)
    (hAB : Disjoint A.val B.val) (hAC : Disjoint A.val C.val)
    (h : missingWordLabel W hW A B hAB = missingWordLabel W hW A C hAC) : B = C := by
  have he : W \ (A.val ∪ B.val) = W \ (A.val ∪ C.val) := by
    rw [missingWordLabel_spec W hW A B hAB, missingWordLabel_spec W hW A C hAC, h]
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    by_contra hn
    have hna : x ∉ A.val := fun ha => disjoint_left.mp hAB ha hx
    have hm : x ∈ W \ (A.val ∪ C.val) := by simp [B.property.1 hx, hna, hn]
    rw [← he] at hm
    exact (mem_sdiff.mp hm).2 (mem_union_right _ hx)
  · intro hx
    by_contra hn
    have hna : x ∉ A.val := fun ha => disjoint_left.mp hAC ha hx
    have hm : x ∈ W \ (A.val ∪ B.val) := by simp [C.property.1 hx, hna, hn]
    rw [he] at hm
    exact (mem_sdiff.mp hm).2 (mem_union_right _ hx)

theorem missingWordLabel_left_injective (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (A C : WordSubset W q) (B : WordSubset W p)
    (hAB : Disjoint A.val B.val) (hCB : Disjoint C.val B.val)
    (h : missingWordLabel W hW A B hAB = missingWordLabel W hW C B hCB) : A = C := by
  have he : W \ (A.val ∪ B.val) = W \ (C.val ∪ B.val) := by
    rw [missingWordLabel_spec W hW A B hAB, missingWordLabel_spec W hW C B hCB, h]
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    by_contra hn
    have hnb : x ∉ B.val := fun hb => disjoint_left.mp hAB hx hb
    have hm : x ∈ W \ (C.val ∪ B.val) := by simp [A.property.1 hx, hnb, hn]
    rw [← he] at hm
    exact (mem_sdiff.mp hm).2 (mem_union_left _ hx)
  · intro hx
    by_contra hn
    have hnb : x ∉ B.val := fun hb => disjoint_left.mp hCB hx hb
    have hm : x ∈ W \ (A.val ∪ B.val) := by simp [C.property.1 hx, hnb, hn]
    rw [he] at hm
    exact (mem_sdiff.mp hm).2 (mem_union_left _ hx)

variable [Fintype α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preservationOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance preservationOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

def preservationProjectionMatrix (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (e : α → H →L[ℂ] H) :
    CStarMatrix (WordSubset W q) (WordSubset W p) (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix fun A B =>
    if hAB : Disjoint A.val B.val then e (missingWordLabel W hW A B hAB) else 0

/-- Distinct missing labels in a row and column give orthogonal ranges
and domains, so the projection part has norm at most one. -/
theorem norm_preservationProjectionMatrix_le (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (e : α → H →L[ℂ] H)
    (he : ∀ a, IsStarProjection (e a)) (horth : ∀ a b, a ≠ b → e a * e b = 0) :
    ‖preservationProjectionMatrix W hW e‖ ≤ 1 := by
  apply norm_projectionMatrix_le_one
  · intro A B
    change IsStarProjection (if hAB : Disjoint A.val B.val then
      e (missingWordLabel W hW A B hAB) else 0)
    split_ifs
    · exact he _
    · exact IsStarProjection.zero _
  · intro A B C hBC
    change (if hAB : Disjoint A.val B.val then e (missingWordLabel W hW A B hAB) else 0) *
      (if hAC : Disjoint A.val C.val then e (missingWordLabel W hW A C hAC) else 0) = 0
    split_ifs with hAB hAC hAC
    · exact horth _ _ (fun h => hBC (missingWordLabel_right_injective W hW A B C hAB hAC h))
    all_goals simp
  · intro B A C hAC
    change (if hAB : Disjoint A.val B.val then e (missingWordLabel W hW A B hAB) else 0) *
      (if hCB : Disjoint C.val B.val then e (missingWordLabel W hW C B hCB) else 0) = 0
    split_ifs with hAB hCB hCB
    · exact horth _ _ (fun h => hAC (missingWordLabel_left_injective W hW A C B hAB hCB h))
    all_goals simp

theorem rectangularOperator_norm_mul_le {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K]
    (S : CStarMatrix I J (H →L[ℂ] H)) (T : CStarMatrix J K (H →L[ℂ] H)) :
    ‖S * T‖ ≤ ‖S‖ * ‖T‖ := by
  rw [← norm_rectangularHilbertMatrix, rectangularHilbertMatrix_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq
    (by rw [norm_rectangularHilbertMatrix, norm_rectangularHilbertMatrix])

def preservationAdjacency (W : Finset α) (p q : ℕ) :
    CStarMatrix (WordSubset W q) (WordSubset W p) (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix fun A B => if Disjoint A.val B.val then 1 else 0

/-- Compression onto the centered GNS leg, including its scalar correction. -/
def preservationSubsetMatrix (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (e : α → H →L[ℂ] H) (P : H →L[ℂ] H) (d : ℝ) :
    CStarMatrix (WordSubset W q) (WordSubset W p) (H →L[ℂ] H) :=
  diagonalAmplification P *
    (preservationProjectionMatrix W hW e - (d⁻¹ : ℂ) • preservationAdjacency W p q) *
    diagonalAmplification P

theorem norm_preservationSubsetMatrix_le (W : Finset α) {p q : ℕ}
    (hW : W.card = p + q + 1) (e : α → H →L[ℂ] H)
    (he : ∀ a, IsStarProjection (e a)) (horth : ∀ a b, a ≠ b → e a * e b = 0)
    (P : H →L[ℂ] H) (hP : IsStarProjection P) {d : ℝ} (hd : 0 < d) :
    ‖preservationSubsetMatrix W hW e P d‖ ≤
      1 + Real.sqrt (((p + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ)) / d := by
  have hPL : ‖diagonalAmplification (n := WordSubset W q) P‖ ≤ 1 :=
    (norm_diagonalAmplification_le P).trans (IsStarProjection.norm_le _ hP)
  have hPR : ‖diagonalAmplification (n := WordSubset W p) P‖ ≤ 1 :=
    (norm_diagonalAmplification_le P).trans (IsStarProjection.norm_le _ hP)
  have hmid : ‖preservationProjectionMatrix W hW e -
      (d⁻¹ : ℂ) • preservationAdjacency (H := H) W p q‖ ≤
      1 + Real.sqrt (((p + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ)) / d := by
    refine (norm_sub_le _ _).trans (add_le_add
      (norm_preservationProjectionMatrix_le W hW e he horth) ?_)
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    calc
      _ ≤ d⁻¹ * Real.sqrt (((p + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (norm_preservation_adjacency_le (H := H) W p q hW)
          (inv_nonneg.mpr hd.le)
      _ = _ := by ring
  unfold preservationSubsetMatrix
  refine (rectangularOperator_norm_mul_le _ _).trans ?_
  calc
    _ ≤ (1 * ‖preservationProjectionMatrix W hW e -
        (d⁻¹ : ℂ) • preservationAdjacency (H := H) W p q‖) * 1 := by
      apply mul_le_mul
      · exact (rectangularOperator_norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right hPL (norm_nonneg _))
      · exact hPR
      · positivity
      · positivity
    _ = _ := by simp
    _ ≤ _ := hmid

end

end KadisonKastler

end OAI
