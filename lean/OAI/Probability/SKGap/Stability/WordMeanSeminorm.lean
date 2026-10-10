import Mathlib
import OAI.Probability.SKGap.Matrix.WordTemplateSurjective
import OAI.Probability.SKGap.Matrix.WordBaseBias

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

lemma actualWord_mean_diagonal (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) :
    matrixEntryMean (fun x : EuclideanSpace ℝ (MatrixCoordinates ι)=>
      actualWord f R hR j a z F (goeMatrix (j/(Fintype.card ι:ℝ)) x))=
      Matrix.diagonal (wordExpected f hR j a z F) := by
  ext i k
  by_cases h : i=k
  · subst k
    simp only [matrixEntryMean,Matrix.diagonal_apply_eq,wordExpected]
  · rw [Matrix.diagonal_apply_ne _ h]
    exact actualWord_offdiag_mean f hR j _ a z F i k h

lemma offDiagonalSeminorm_sub_diagonal (M : Matrix ι ι ℝ) (d : ι→ℝ) :
    offDiagonalSeminorm (M-Matrix.diagonal d)=offDiagonalSeminorm M := by
  change ‖offDiagonalVector (M-Matrix.diagonal d)‖=‖offDiagonalVector M‖
  apply congrArg norm
  ext p
  simp only [offDiagonalVector,WithLp.ofLp_toLp,Matrix.sub_apply]
  split_ifs with h
  · rfl
  · simp only [Matrix.diagonal_apply_ne _ h,sub_zero]

lemma offDiagonalSeminorm_diagonal (d : ι→ℝ) :
    offDiagonalSeminorm (Matrix.diagonal d)=0 := by
  have he : offDiagonalVector (Matrix.diagonal d)=0 := by
    ext p
    simp only [offDiagonalVector,WithLp.ofLp_toLp,PiLp.zero_apply]
    split_ifs with h
    · rfl
    · exact Matrix.diagonal_apply_ne _ h
  change ‖offDiagonalVector (Matrix.diagonal d)‖=0
  rw [he,norm_zero]

lemma diagonalSeminorm_diagonal_bound {n : ℕ} (hn : 1≤n) {C : ℝ} (hC : 0≤C)
    {d : Fin n→ℝ} (hd : ∀ i,|d i|≤C/(n:ℝ)) :
    diagonalSeminorm (Matrix.diagonal d)≤C := by
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := lt_of_lt_of_le zero_lt_one hnr
  apply le_of_pow_le_pow_left₀ (by decide : 2≠0) hC
  rw [diagonalSeminorm_sq]
  have hi (i : Fin n) : (Matrix.diagonal d i i)^2≤(C/(n:ℝ))^2 := by
    rw [Matrix.diagonal_apply_eq,←sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hd i) 2
  calc
    _ ≤ ∑ i : Fin n,(C/(n:ℝ))^2 := Finset.sum_le_sum (fun i _=>hi i)
    _ = C^2/(n:ℝ) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];field_simp
    _ ≤ C^2 := (div_le_self (sq_nonneg _) hnr)

lemma actualWord_diagonal_prediction_decompose (f : 𝓢(ℝ,ℂ)) {R j : ℝ} (hR : 0≤R)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (g : MatrixCoordinates ι→ℝ) :
    actualWord f R hR j a z F (goeMatrix (j/(Fintype.card ι:ℝ)) g)-
      Matrix.diagonal (wordPrediction j a z F)=
      matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates ι)=>actualWord f R hR j a z F
        (goeMatrix (j/(Fintype.card ι:ℝ)) x)) (WithLp.toLp 2 g)+
      Matrix.diagonal (fun i=>wordExpected f hR j a z F i-wordPrediction j a z F i) := by
  rw [matrixCentered,actualWord_mean_diagonal]
  ext i k
  by_cases h : i=k
  · subst k
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.diagonal_apply_eq]
    ring
  · simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.diagonal_apply_ne _ h,sub_zero,add_zero]
end SKGap
end
end

end OAI
