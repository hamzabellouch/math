import OAI.Probability.InvariantIsing.Cavity.CavityBaseEigenspaces

namespace OAI

/-! The base interaction has an explicit spectral decomposition. Its
retained multiplicities and the assigned special multiplicities add to
the required base counts. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityBaseReplacement_spectral_sum {r s d : ℕ} {ι : Type*} [Fintype ι]
    (J : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin s) ℝ)
    (D : Matrix (Fin s) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin r) ι ℝ) (L : Matrix ι ι ℝ)
    (hJR : J * R = R * L) (hJW : J * W = W * D)
    (hcomplete : R * R.transpose + W * W.transpose = 1) :
    cavityBaseReplacement J W D B A₀ =
      R * L * R.transpose + (W * B) * A₀ * (W * B).transpose := by
  have hJ : J = R * L * R.transpose + W * D * W.transpose := by
    calc
      J = J * (R * R.transpose + W * W.transpose) := by rw [hcomplete, Matrix.mul_one]
      _ = _ := by rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJR, hJW]
  unfold cavityBaseReplacement
  rw [hJ]
  abel

lemma cavityRetainedStack_perp {r m n : ℕ} (k : Fin m → ℕ)
    (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (hRX : ∀ a b, (R a).transpose * cavityNormalizeFrame (X b) = 0) :
    (cavityRetainedStack k R).transpose * cavityEigenspaceFrame X = 0 := by
  ext ⟨a, i⟩ j
  exact congrArg (fun M : Matrix (Fin (k a)) (Fin n) ℝ =>
    M i (finProdFinEquiv.symm j).2) (hRX a (finProdFinEquiv.symm j).1)

lemma cavityRetainedStack_eigen {r m : ℕ} (g : Fin r → Fin m) (lam : Fin m → ℝ)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a i, g i ≠ a → ∀ j, R a i j = 0) :
    Matrix.diagonal (fun i => lam (g i)) * cavityRetainedStack k R =
      cavityRetainedStack k R * Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) := by
  ext i ⟨a, j⟩
  have h := congrArg (fun M : Matrix (Fin r) (Fin (k a)) ℝ => M i j)
    (cavitySpectralSupport_eigen g a lam (R a) (hR a))
  rw [Matrix.mul_diagonal]
  simpa only [Matrix.diagonal_mul, cavityRetainedStack, Matrix.smul_apply,
    smul_eq_mul, mul_comm] using h

theorem cavityBase_spectral_decomposition {r m n d : ℕ}
    (g : Fin r → Fin m) (A : Matrix (Fin r) (Fin n) ℝ) (lam : Fin m → ℝ)
    (k : Fin m → ℕ) (R : (a : Fin m) → Matrix (Fin r) (Fin (k a)) ℝ)
    (hR : ∀ a i, g i ≠ a → ∀ j, R a i j = 0)
    (hproj : ∀ a, R a * (R a).transpose +
      cavityNormalizeFrame (cavitySpectralImage g A a) *
        (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0))
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i)))
      (cavityEigenspaceFrame (cavitySpectralImage g A)) (cavityRepeatedSpectrum (n := n) lam) B A₀ =
        cavityRetainedStack k R * Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) *
          (cavityRetainedStack k R).transpose +
        (cavityEigenspaceFrame (cavitySpectralImage g A) * B) * A₀ *
          (cavityEigenspaceFrame (cavitySpectralImage g A) * B).transpose := by
  apply cavityBaseReplacement_spectral_sum
  · exact cavityRetainedStack_eigen g lam k R hR
  · exact cavityEigenspaceFrame_eigen _ _ lam (cavitySpectralImage_eigen g A lam)
  · exact cavityRetainedStack_complete g A k R hproj

end InvariantIsing

end

end OAI
