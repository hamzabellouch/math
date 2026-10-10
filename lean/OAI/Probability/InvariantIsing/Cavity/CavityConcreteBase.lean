import OAI.Probability.InvariantIsing.Cavity.CavityReservoirFrame

namespace OAI

/-! The concrete spectral-image construction gives the prescribed base
spectral orbit. No retained eigenbasis is chosen in the definition of the
base interaction; its existence is used only to establish the orbit. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavityConcreteBase_spectral_orbit {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N + n) // g i = a} ≃ Fin (k a + n))
    (e : ((a : Fin m) × Fin (k a)) ⊕ Fin d ≃ Fin N)
    (U : Orthogonal (N + n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (T : Matrix (Fin (m * n)) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hBT : B.transpose * T = 0)
    (hT : T = cavitySpectralStack (fun a =>
      (cavitySpectralImage g (fun i j => (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
        i (Fin.natAdd N j)) a).transpose *
      cavitySpectralImage g (fun i j => (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
        i (Fin.natAdd N j)) a))
    (hA : ∀ a, ((cavitySpectralImage g
      (fun i j => (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j)) a).transpose *
      cavitySpectralImage g
        (fun i j => (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j)) a).PosDef) :
    ∃ V : Orthogonal N,
      ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
        cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i)))
          (cavityEigenspaceFrame (cavitySpectralImage g
            (fun i j => (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j))))
          (cavityRepeatedSpectrum (n := n) lam) B (Matrix.diagonal lam₀) *
        (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).submatrix
          (Fin.castAdd n) (Fin.castAdd n) =
      (V : Matrix (Fin N) (Fin N) ℝ) *
        Matrix.diagonal (fun j => Sum.elim (fun a => lam a.1) lam₀ (e.symm j)) *
          (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
  classical
  let A : Matrix (Fin (N + n)) (Fin n) ℝ :=
    fun i j => (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j)
  let X := cavitySpectralImage g A
  choose R hRG hRX hRS hRP using fun a => cavityRetainedFrame_exists g A a (ek a) (hA a)
  have hcross : ∀ a b, a ≠ b → (R a).transpose * R b = 0 := by
    intro a b hab
    exact cavitySpectralSupport_crossGram g a b hab (R a) (R b) (hRS a) (hRS b)
  have hperp : ∀ a b, (R a).transpose * cavityNormalizeFrame (X b) = 0 := by
    intro a b
    by_cases hab : a = b
    · subst b
      have h := congrArg Matrix.transpose (hRX a)
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
    · exact cavitySpectralSupport_crossGram g a b hab (R a) _ (hRS a)
        (cavityNormalizeFrame_spectral_support g A b)
  apply cavityBaseReplacement_physical_orbit e U _ (cavityRetainedStack k R)
    (cavityEigenspaceFrame X) _ B T (fun a => lam a.1) lam₀
  · exact cavityRetainedStack_gram k R hRG hcross
  · exact cavityEigenspaceFrame_gram X hA (cavitySpectralImage_crossGram g A)
  · exact cavityRetainedStack_perp k R X hperp
  · exact hB
  · exact hBT
  · rw [hT, cavityEigenspaceFrame_stack X hA]
    exact cavitySpectralImage_sum g A
  · exact cavityRetainedStack_eigen g lam k R hRS
  · exact cavityEigenspaceFrame_eigen _ X lam (cavitySpectralImage_eigen g A lam)
  · exact cavityRetainedStack_complete g A k R hRP

end InvariantIsing

end

end OAI
