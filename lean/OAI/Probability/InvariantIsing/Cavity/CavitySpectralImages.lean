import OAI.Probability.InvariantIsing.Cavity.CavityCouplingAlgebra
import OAI.Probability.InvariantIsing.Cavity.CavityWindowGram

namespace OAI

/-! The separate spectral images of the cavity columns. These are the
concrete inputs to the normalized-frame coupling construction. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavitySpectralImage {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m) : Matrix (Fin r) (Fin n) ℝ :=
  fun i j => if g i = a then A i j else 0

lemma cavitySpectralImage_sum {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) : ∑ a, cavitySpectralImage g A a = A := by
  ext i j
  simp only [Matrix.sum_apply, cavitySpectralImage, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

lemma cavitySpectralImage_crossGram {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (a b : Fin m) (hab : a ≠ b) :
    (cavitySpectralImage g A a).transpose * cavitySpectralImage g A b = 0 := by
  ext i j
  change (∑ k : Fin r, (if g k = a then A k i else 0) *
    (if g k = b then A k j else 0)) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases ha : g k = a
  · simp only [ha, hab, ite_true, ite_false, mul_zero]
  · simp only [ha, ite_false, zero_mul]

lemma cavitySpectralImage_gram {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m) :
    (cavitySpectralImage g A a).transpose * cavitySpectralImage g A a =
      A.transpose * Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0) * A := by
  ext i j
  change (∑ k : Fin r, (if g k = a then A k i else 0) *
    (if g k = a then A k j else 0)) =
    ∑ k : Fin r, (∑ t : Fin r,
      A t i * (if t = k then (if g t = a then (1 : ℝ) else 0) else 0)) * A k j
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

lemma cavitySpectralImage_eigen {r m n : ℕ} (g : Fin r → Fin m)
    (A : Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ) (a : Fin m) :
    Matrix.diagonal (fun i => lam (g i)) * cavitySpectralImage g A a =
      lam a • cavitySpectralImage g A a := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.smul_apply]
  change lam (g i) * (if g i = a then A i j else 0) =
    lam a * (if g i = a then A i j else 0)
  split_ifs with h
  · rw [h]
  · rw [mul_zero, mul_zero]

lemma measurable_cavitySpectralImage {r m n : ℕ} (g : Fin r → Fin m) (a : Fin m) :
    Measurable (fun A : Matrix (Fin r) (Fin n) ℝ => cavitySpectralImage g A a) := by
  apply Measurable.of_eval_matrix
  intro i j
  by_cases h : g i = a
  · simpa only [cavitySpectralImage, h, ite_true] using
      (Matrix.measurable_apply (i := i) (j := j))
  · simpa only [cavitySpectralImage, h, ite_false] using
      (measurable_const : Measurable (fun _ : Matrix (Fin r) (Fin n) ℝ => (0 : ℝ)))

theorem cavitySpectralImage_coupling_blocks {r m n d : ℕ}
    (g : Fin r → Fin m) (A : Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ)
    (hA : ∀ a, ((cavitySpectralImage g A a).transpose * cavitySpectralImage g A a).PosDef)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) :
    cavitySpecialBlocks (Matrix.diagonal (fun i => lam (g i)))
      (cavityEigenspaceFrame (cavitySpectralImage g A) * B) A =
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavitySpectralStack (fun a => (cavitySpectralImage g A a).transpose *
          cavitySpectralImage g A a)) := by
  have h := cavityEigenspaceFrame_blocks _ _ lam hA
    (cavitySpectralImage_crossGram g A) (cavitySpectralImage_eigen g A lam) B
  simpa only [cavitySpectralImage_sum] using h

end InvariantIsing

end

end OAI
