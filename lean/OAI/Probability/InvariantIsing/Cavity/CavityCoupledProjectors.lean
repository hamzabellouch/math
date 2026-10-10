import OAI.Probability.InvariantIsing.Cavity.CavityBaseOverlap
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledProjectors

namespace OAI

/-! The physical overlap comparison uses the same frame as the entire
family of labeled spectral projectors, including repeated eigenvalues. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavity_coupled_labeled_projectors {N n m d : ℕ} (hN : 0 < N)
    (g : Fin (N + n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N + n) // g i = a} ≃ Fin (k a + n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m * n) ≃ Fin (d + n))
    (U : SpecialOrthogonal (N + n)) (a₀ : Fin d → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef) :
    ∃ V : Orthogonal N,
      (∀ (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ),
        cavityPhysicalBase g lam B (Matrix.diagonal lam₀) (cavitySpecialOrthogonal U) =
          (V : Matrix (Fin N) (Fin N) ℝ) *
            Matrix.diagonal (fun j => Sum.elim (fun w => lam w.1) lam₀ (e.symm j)) *
            (V : Matrix (Fin N) (Fin N) ℝ).transpose) ∧
      cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal U) =
        cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) ∧
      cavityPhysicalSpecial g B (cavitySpecialOrthogonal U) =
        (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e ∧
      ∀ a σ τ,
        |projectedOverlap (specialRotation U) (cavitySpectralGroup g a) σ τ -
          projectedOverlap (matrixRotation V⁻¹) (cavityBaseGroup k e a₀ a)
            (fun i => σ (Fin.castAdd n i)) (fun i => τ (Fin.castAdd n i))| ≤
        ((2 * (n : ℝ) + 1) / N) *
          (1 + ‖cavityFullSpecialCoordinates g
              (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U σ‖ ^ 2 +
            ‖cavityFullSpecialCoordinates g
              (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U τ‖ ^ 2) := by
  classical
  let O := cavitySpecialOrthogonal U
  let A := cavityColumns O
  let X := cavitySpectralImage g A
  let W := cavityEigenspaceFrame X
  let B₁ := B (cavityCompressionGrams g O)
  let T := cavitySpectralStack (cavityCompressionGrams g O)
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
  let S := cavityRetainedStack k R
  let F := Matrix.fromCols S (W * B₁)
  let P := (O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F
  have hWG : W.transpose * W = 1 :=
    cavityEigenspaceFrame_gram X hA (cavitySpectralImage_crossGram g A)
  have hSG : S.transpose * S = 1 := cavityRetainedStack_gram k R hRG hcross
  have hSW : S.transpose * W = 0 := cavityRetainedStack_perp k R X hperp
  have hWT : W * T = A :=
    (cavityEigenspaceFrame_stack X hA).trans (cavitySpectralImage_sum g A)
  have hFG : F.transpose * F = 1 := cavityBaseFrame_gram S W B₁ hSG hWG hSW hB
  have hPG : P.transpose * P = 1 := (cavityPhysicalFrame_gram O F).trans hFG
  have hPF : ∀ i : Fin n, ∀ j, P (Fin.natAdd N i) j = 0 := by
    apply cavityPhysicalFrame_lastRows (O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) F
    change A.transpose * F = 0
    rw [← hWT]
    exact cavityBaseFrame_cavity_perp S W B₁ T hWG hSW hBT
  obtain ⟨V, hV⟩ := cavityReservoirRows_orthogonal e P hPG hPF
  have hSpectrum (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ) :
      cavityPhysicalBase g lam B (Matrix.diagonal lam₀) O =
        (V : Matrix (Fin N) (Fin N) ℝ) *
          Matrix.diagonal (fun j => Sum.elim (fun w => lam w.1) lam₀ (e.symm j)) *
          (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
    let Λ := Matrix.diagonal (Sum.elim (fun v : (b : Fin m) × Fin (k b) => lam v.1) lam₀)
    have hJ : cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i))) W
        (cavityRepeatedSpectrum (n := n) lam) B₁ (Matrix.diagonal lam₀) =
        F * Λ * F.transpose := by
      rw [cavityBase_spectral_decomposition g A lam k R hRS hRP]
      exact (cavityBaseFrame_spectral_sum S (W * B₁) (fun v => lam v.1) lam₀).symm
    have hJP : (O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
        cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i))) W
          (cavityRepeatedSpectrum (n := n) lam) B₁ (Matrix.diagonal lam₀) *
        (O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) = P * Λ * P.transpose := by
      rw [hJ]
      simp only [P, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    change ((O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
      cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i))) W
        (cavityRepeatedSpectrum (n := n) lam) B₁ (Matrix.diagonal lam₀) *
      (O : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).submatrix
        (Fin.castAdd n) (Fin.castAdd n) = _
    rw [hJP, cavityReservoirRows_conjugate]
    exact cavityReservoir_spectral_eq e P _ V hV
  have hSpecial : cavityPhysicalSpecial g B O =
      (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e := by
    ext i j
    rw [cavityCanonicalSpecial_mul, hV]
    simp only [Equiv.symm_apply_apply]
    rfl
  refine ⟨V, hSpectrum, ?_, hSpecial, ?_⟩
  · apply Prod.ext
    · funext a
      exact hSpectrum (fun b => if b=a then 1 else 0) (fun j => if a₀ j=a then 1 else 0)
    · exact hSpecial
  · intro a σ τ
    rw [cavity_base_group_overlap g U B₁ k R e a₀ hPF V hV a σ τ]
    exact cavity_retained_base_comparison hN g es U B₁ hB hBT hA k R hRP
      (fun a => Finset.univ.filter (fun j => a₀ j = a)) a σ τ

end InvariantIsing

end

end OAI
