import Mathlib
import OAI.Analysis.LaughlinGap.RationalCreatedGram
import OAI.Analysis.LaughlinGap.RationalFourRows

namespace OAI

/-! Rational Four Certificate. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin

variable {ι : Type*} [Fintype ι]

def copyNormalizationSq (D r : ℕ) : ℚ := 1 / ((r.factorial:ℚ)*(D-r).factorial)

lemma copyNormalization_sq (D r : ℕ) :
    copyNormalization D r ^ 2 = (copyNormalizationSq D r:ℝ) := by
  simp [copyNormalization,copyNormalizationSq,mul_pow]

def rationalFourComparison (rows : ι → RationalRow) (ε : ℚ) (D : ℕ) :
    Matrix (FourCopy D) (FourCopy D) ℚ := fun u v =>
  (if u=v then ((if u.val.val=1 then 2 else 0)+ε)*copyNormalizationSq D u.val.val else 0) -
    copyNormalizationSq D u.val.val * (∑ a, (rows a).fourMatrix D u v) *
      copyNormalizationSq D v.val.val

def rationalFourCompression (rows : ι → RationalRow) (ε : ℚ) {D : ℕ} (hD : D ≤ 23) :
    Matrix (FourCopy D) (FourCopy D) ℚ :=
  rationalCreatedGram hD * rationalFourComparison rows ε D * rationalCreatedGram hD

noncomputable def copyDiagonal (D : ℕ) : Matrix (FourCopy D) (FourCopy D) ℂ :=
  Matrix.diagonal (fun r => (copyNormalization D r.val.val:ℂ))

lemma createdGram_eq_diagonal {D : ℕ} (hD : D ≤ 23) :
    Occupation.createdGram (fourLocalHighestStar hD) =
      copyDiagonal D * (rationalCreatedGram hD).map (algebraMap ℚ ℂ) * copyDiagonal D := by
  ext u v
  simp only [copyDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.map_apply]
  rw [createdGram_rational]
  push_cast
  rfl

lemma rationalFourComparison_real (rows : ι → RationalRow) (ε : ℚ) (D : ℕ) :
    (rationalFourComparison rows ε D).map (algebraMap ℚ ℝ) =
      Matrix.diagonal (fun u : FourCopy D => copyNormalization D u.val.val) *
        fourComparisonStar (fun a => (rows a).toReal) (ε:ℝ) D *
      Matrix.diagonal (fun u : FourCopy D => copyNormalization D u.val.val) := by
  ext u v
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.map_apply,
    rationalFourComparison,fourComparisonStar,Matrix.add_apply,Matrix.sub_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,RationalRow.fourMatrix_eq]
  change (((if u=v then ((if u.val.val=1 then 2 else 0)+ε)*copyNormalizationSq D u.val.val else 0) -
      copyNormalizationSq D u.val.val * (∑ a, (rows a).fourMatrix D u v) *
        copyNormalizationSq D v.val.val : ℚ) : ℝ) = _
  by_cases h : u=v
  · subst v
    simp only [ite_true,Matrix.one_apply_eq,mul_one,fourCopyTarget,and_self]
    by_cases hu : u.val.val=1
    all_goals simp only [hu,ite_true,ite_false]; push_cast
    all_goals simp only [← Finset.mul_sum,← Finset.sum_mul,← copyNormalization_sq]; ring
  · have ht : ¬ (u.val.val=1 ∧ v.val.val=1) := by
      rintro ⟨hu,hv⟩
      exact h (Subtype.ext (Fin.ext (hu.trans hv.symm)))
    simp only [ite_eq_right h,Matrix.one_apply_ne h,mul_zero,add_zero,fourCopyTarget,ite_eq_right ht,
      zero_sub]
    push_cast
    simp only [← Finset.mul_sum,← Finset.sum_mul,← copyNormalization_sq]
    ring

lemma rationalFourComparison_eq (rows : ι → RationalRow) (ε : ℚ) (D : ℕ) :
    (rationalFourComparison rows ε D).map (algebraMap ℚ ℂ) =
      copyDiagonal D * (fourComparisonStar (fun a => (rows a).toReal) (ε:ℝ) D).map
        (algebraMap ℝ ℂ) * copyDiagonal D := by
  have h := congrArg (fun A : Matrix (FourCopy D) (FourCopy D) ℝ =>
    A.map (algebraMap ℝ ℂ)) (rationalFourComparison_real rows ε D)
  convert h using 1
  · ext u v
    simp [Matrix.map_apply]
  · simp only [Matrix.map_mul,Matrix.diagonal_map (map_zero _)]
    rfl

lemma fourCertificate_of_rational (rows : ι → RationalRow) (ε : ℚ) {D : ℕ} (hD : D ≤ 23)
    (h : ((rationalFourCompression rows ε hD).map (algebraMap ℚ ℂ)).PosSemidef) :
    FourCertificate (fun a => (rows a).toReal) (ε:ℝ) D hD := by
  have he : (copyDiagonal D).conjTranspose=copyDiagonal D := by
    simp [copyDiagonal]
  have hp := h.mul_mul_conjTranspose_same (copyDiagonal D)
  rw [he] at hp
  unfold FourCertificate
  rw [createdGram_eq_diagonal]
  convert hp using 1
  rw [rationalFourCompression,Matrix.map_mul,Matrix.map_mul,rationalFourComparison_eq]
  simp only [Matrix.mul_assoc]

lemma rational_ldl_positive {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M L : Matrix κ κ ℚ) (d : κ → ℚ) (hd : ∀ i, 0 ≤ d i)
    (he : M = L * Matrix.diagonal d * L.transpose) :
    (M.map (algebraMap ℚ ℂ)).PosSemidef := by
  have hp : (Matrix.diagonal (fun i => (d i:ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    simpa only [← Complex.ofReal_ratCast,Complex.nonneg_iff,Complex.ofReal_re,Complex.ofReal_im,
      and_true] using (Rat.cast_nonneg (K := ℝ)).mpr (hd i)
  have hh := hp.mul_mul_conjTranspose_same (L.map (algebraMap ℚ ℂ))
  convert hh using 1
  rw [he,Matrix.map_mul,Matrix.map_mul]
  congr 1
  · congr 1
    ext i j
    by_cases h : i=j <;> simp [h]
  · ext i j
    simp [Matrix.conjTranspose_apply]

end LaughlinGap.RealOccupation

end

end OAI
