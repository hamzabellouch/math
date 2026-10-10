import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open Matrix
open scoped BigOperators

variable {n : ℕ}

lemma whiten_entry_bound {c ai aj bi wi zj t : ℝ} (hc : 0 < c)
    (haj : 0 < aj) (hbi : 0 ≤ bi) (hwi : 0 ≤ wi) (hzj : 0 < zj)
    (ht : 0 ≤ t) (hab : ai*bi ≤ c⁻¹^2) (htsq : t^2 ≤ c*ai*aj*t) :
    (bi*wi)*t^2/(aj*zj) ≤ (wi*t)/(c*zj) := by
  have hc0 := ne_of_gt hc
  have hcoef : c*ai*bi ≤ c⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hab hc.le
    calc
      _ = c*(ai*bi) := by ring
      _ ≤ c*c⁻¹^2 := h
      _ = c⁻¹ := by field_simp
  calc
    _ ≤ (bi*wi)*(c*ai*aj*t)/(aj*zj) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htsq (mul_nonneg hbi hwi))
        (mul_pos haj hzj).le
    _ = (c*ai*bi)*(wi*t)/zj := by field_simp
    _ ≤ c⁻¹*(wi*t)/zj :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (mul_nonneg hwi ht)) hzj.le
    _ = (wi*t)/(c*zj) := by ring

theorem weighted_frobenius_bound {c : ℝ} (hc : 0 < c)
    (a b z w : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 ≤ b i)
    (hz : ∀ i, 0 < z i) (hw : ∀ i, 0 ≤ w i)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (hm : ∀ i j, 0 ≤ M i j)
    (hab : ∀ i, a i*b i ≤ c⁻¹^2)
    (hsq : ∀ i j, (M i j)^2 ≤ c*a i*a j*M i j)
    (hdual : ∀ i, (M *ᵥ w) i ≤ z i) :
    (∑ i, ∑ j, (b i*w i)*(M i j)^2/(a j*z j)) ≤ (n : ℝ)/c := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j : Fin n, (1/c : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ i : Fin n, (w i*M i j)/(c*z j) := by
          apply Finset.sum_le_sum
          intro i _
          exact whiten_entry_bound hc (ha j) (hb i) (hw i) (hz j) (hm i j) (hab i) (hsq i j)
        _ = (M *ᵥ w) j/(c*z j) := by
          rw [← Finset.sum_div]
          congr 1
          unfold Matrix.mulVec dotProduct
          apply Finset.sum_congr rfl
          intro i _
          have he : M i j = M j i := by simpa using (hM.apply i j).symm
          rw [he,mul_comm]
        _ ≤ z j/(c*z j) := div_le_div_of_nonneg_right (hdual j) (mul_pos hc (hz j)).le
        _ = 1/c := by field_simp [ne_of_gt (hz j)]
    _ = _ := by simp [div_eq_mul_inv]

def whitenWeighted (a b : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => Real.sqrt (b i)*M i j/Real.sqrt (a j)

lemma whitenWeighted_sq (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (whitenWeighted a b M i j)^2 = b i*(M i j)^2/a j := by
  simp only [whitenWeighted,div_pow,mul_pow,Real.sq_sqrt (hb i),Real.sq_sqrt (ha j)]

lemma gram_trace_sum_squares (M : Matrix (Fin n) (Fin n) ℝ) :
    (M.conjTranspose*M).trace = ∑ i, ∑ j, (M i j)^2 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma whitenWeighted_trace (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ((whitenWeighted a b M).conjTranspose * whitenWeighted a b M).trace =
      ∑ i, ∑ j, b i*(M i j)^2/a j := by
  rw [gram_trace_sum_squares]
  simp only [whitenWeighted_sq a b ha hb]

end
end CurrentKS.Covariance

end OAI
