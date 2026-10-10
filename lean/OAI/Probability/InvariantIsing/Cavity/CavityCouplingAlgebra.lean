import OAI.Probability.InvariantIsing.Cavity.CavitySpecialBlocks
import OAI.Probability.InvariantIsing.Cavity.CavityMeasurableComplement
import OAI.Probability.InvariantIsing.Cavity.CavityFrameRotation

namespace OAI

/-! The orthogonal spectral directions in the finite cavity coupling.
Each spectral image of the cavity columns is normalized separately.
The resulting frame carries the small square-root stack isometrically
back to the original cavity columns. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityNormalizeFrame_mul_sqrt {r n : ℕ}
    (X : Matrix (Fin r) (Fin n) ℝ) (hX : (X.transpose * X).PosDef) :
    cavityNormalizeFrame X * CFC.sqrt (X.transpose * X) = X := by
  rw [cavityNormalizeFrame, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (cavity_sqrt_det_isUnit _ hX), Matrix.mul_one]

lemma cavityNormalizeFrame_crossGram {r n : ℕ}
    (X Y : Matrix (Fin r) (Fin n) ℝ) (hXY : X.transpose * Y = 0) :
    (cavityNormalizeFrame X).transpose * cavityNormalizeFrame Y = 0 := by
  simp only [cavityNormalizeFrame, Matrix.transpose_mul]
  calc
    _ = ((CFC.sqrt (X.transpose * X))⁻¹).transpose *
        (X.transpose * Y) * (CFC.sqrt (Y.transpose * Y))⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hXY, Matrix.mul_zero, Matrix.zero_mul]

def cavityEigenspaceFrame {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) : Matrix (Fin r) (Fin (m * n)) ℝ :=
  fun i j => cavityNormalizeFrame (X (finProdFinEquiv.symm j).1)
    i (finProdFinEquiv.symm j).2

theorem cavityEigenspaceFrame_gram {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef)
    (hXY : ∀ a b, a ≠ b → (X a).transpose * X b = 0) :
    (cavityEigenspaceFrame X).transpose * cavityEigenspaceFrame X = 1 := by
  classical
  ext i j
  let a := (finProdFinEquiv.symm i).1
  let b := (finProdFinEquiv.symm j).1
  let s := (finProdFinEquiv.symm i).2
  let t := (finProdFinEquiv.symm j).2
  change ((cavityNormalizeFrame (X a)).transpose * cavityNormalizeFrame (X b)) s t =
    if i = j then 1 else 0
  by_cases hab : a = b
  · rw [← hab, cavityNormalizeFrame_gram _ (hX a), Matrix.one_apply]
    have hij : i = j ↔ s = t := by
      constructor
      · intro h; subst j; rfl
      · intro h
        apply (finProdFinEquiv.symm : Fin (m * n) ≃ Fin m × Fin n).injective
        exact Prod.ext hab h
    simp only [hij]
  · rw [cavityNormalizeFrame_crossGram _ _ (hXY a b hab), Matrix.zero_apply]
    have hij : i ≠ j := by
      intro h; subst j; exact hab rfl
    simp only [hij, ite_false]

theorem cavityEigenspaceFrame_stack {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef) :
    cavityEigenspaceFrame X * cavitySpectralStack (fun a => (X a).transpose * X a) =
      ∑ a, X a := by
  ext i j
  change (∑ k : Fin (m * n), cavityNormalizeFrame (X (finProdFinEquiv.symm k).1)
    i (finProdFinEquiv.symm k).2 *
    CFC.sqrt ((X (finProdFinEquiv.symm k).1).transpose * X (finProdFinEquiv.symm k).1)
      (finProdFinEquiv.symm k).2 j) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun A : Matrix (Fin r) (Fin n) ℝ => A i j)
    (cavityNormalizeFrame_mul_sqrt (X a) (hX a))

lemma cavityNormalizeFrame_eigen {r n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (X : Matrix (Fin r) (Fin n) ℝ)
    (lam : ℝ) (hDX : D * X = lam • X) :
    D * cavityNormalizeFrame X = lam • cavityNormalizeFrame X := by
  simp only [cavityNormalizeFrame, ← Matrix.mul_assoc, hDX, Matrix.smul_mul]

theorem cavityEigenspaceFrame_eigen {r m n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ)
    (hDX : ∀ a, D * X a = lam a • X a) :
    D * cavityEigenspaceFrame X =
      cavityEigenspaceFrame X * cavityRepeatedSpectrum (n := n) lam := by
  ext i j
  have h := congrArg (fun A : Matrix (Fin r) (Fin n) ℝ =>
    A i (finProdFinEquiv.symm j).2)
      (cavityNormalizeFrame_eigen D (X (finProdFinEquiv.symm j).1)
        (lam (finProdFinEquiv.symm j).1) (hDX _))
  change (∑ k, D i k * cavityNormalizeFrame (X (finProdFinEquiv.symm j).1)
    k (finProdFinEquiv.symm j).2) = _ at h
  rw [cavityRepeatedSpectrum, Matrix.mul_diagonal]
  simpa only [Matrix.mul_apply, cavityEigenspaceFrame, Matrix.smul_apply, smul_eq_mul,
    mul_comm] using h

theorem cavityEigenspaceFrame_compression {r m n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef)
    (hXY : ∀ a b, a ≠ b → (X a).transpose * X b = 0)
    (hDX : ∀ a, D * X a = lam a • X a) :
    (cavityEigenspaceFrame X).transpose * D * cavityEigenspaceFrame X =
      cavityRepeatedSpectrum (n := n) lam := by
  rw [Matrix.mul_assoc, cavityEigenspaceFrame_eigen D X lam hDX,
    ← Matrix.mul_assoc, cavityEigenspaceFrame_gram X hX hXY, Matrix.one_mul]

theorem cavityEigenspaceFrame_special_gram {r m n d : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef)
    (hXY : ∀ a b, a ≠ b → (X a).transpose * X b = 0)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1) :
    (cavityEigenspaceFrame X * B).transpose * (cavityEigenspaceFrame X * B) = 1 := by
  rw [Matrix.transpose_mul]
  calc
    _ = B.transpose * ((cavityEigenspaceFrame X).transpose * cavityEigenspaceFrame X) * B := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [cavityEigenspaceFrame_gram X hX hXY, Matrix.mul_one, hB]

theorem cavityEigenspaceFrame_special_perp {r m n d : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef)
    (hXY : ∀ a b, a ≠ b → (X a).transpose * X b = 0)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : B.transpose * cavitySpectralStack (fun a => (X a).transpose * X a) = 0) :
    (cavityEigenspaceFrame X * B).transpose * (∑ a, X a) = 0 := by
  rw [← cavityEigenspaceFrame_stack X hX, Matrix.transpose_mul]
  calc
    _ = B.transpose * ((cavityEigenspaceFrame X).transpose * cavityEigenspaceFrame X) *
        cavitySpectralStack (fun a => (X a).transpose * X a) := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [cavityEigenspaceFrame_gram X hX hXY, Matrix.mul_one, hB]

lemma cavitySpecialBlocks_pullback {r s d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (E : Matrix (Fin s) (Fin n) ℝ) :
    cavitySpecialBlocks D (W * B) (W * E) =
      cavitySpecialBlocks (W.transpose * D * W) B E := by
  simp only [cavitySpecialBlocks, Matrix.transpose_mul, Matrix.mul_assoc]

theorem cavityEigenspaceFrame_blocks {r m n d : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ)
    (hX : ∀ a, ((X a).transpose * X a).PosDef)
    (hXY : ∀ a b, a ≠ b → (X a).transpose * X b = 0)
    (hDX : ∀ a, D * X a = lam a • X a)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) :
    cavitySpecialBlocks D (cavityEigenspaceFrame X * B) (∑ a, X a) =
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavitySpectralStack (fun a => (X a).transpose * X a)) := by
  rw [← cavityEigenspaceFrame_stack X hX, cavitySpecialBlocks_pullback,
    cavityEigenspaceFrame_compression D X lam hX hXY hDX]

lemma measurable_cavityEigenspaceFrame (r m n : ℕ) :
    Measurable (cavityEigenspaceFrame :
      (Fin m → Matrix (Fin r) (Fin n) ℝ) → Matrix (Fin r) (Fin (m * n)) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact ((measurable_cavityNormalizeFrame r n).comp
    (measurable_pi_apply (finProdFinEquiv.symm j).1)).eval_matrix

lemma cavityEigenspaceFrame_left_orthogonal {r m n : ℕ}
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (U : Matrix (Fin r) (Fin r) ℝ) (hU : U.transpose * U = 1) :
    cavityEigenspaceFrame (fun a => U * X a) = U * cavityEigenspaceFrame X := by
  ext i j
  change cavityNormalizeFrame (U * X (finProdFinEquiv.symm j).1)
    i (finProdFinEquiv.symm j).2 = _
  rw [cavityNormalizeFrame_left_orthogonal _ U hU]
  rfl

end InvariantIsing

end

end OAI
