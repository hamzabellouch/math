import OAI.Probability.InvariantIsing.Cavity.CavityConcreteFrameOrbit
import OAI.Probability.InvariantIsing.Cavity.CavityBaseHaarFactorization

namespace OAI

/-! A single physical eigenframe represents every assignment of the
spectral values. In particular it retains the labeled spectral
projectors even when two physical eigenvalues coincide. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavityBaseFrame_simultaneous_orbit {N n s d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : (ι ⊕ Fin d) ≃ Fin N)
    (U : Orthogonal (N+n)) (R : Matrix (Fin (N+n)) ι ℝ)
    (W : Matrix (Fin (N+n)) (Fin s) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (T : Matrix (Fin s) (Fin n) ℝ)
    (hR : R.transpose * R = 1) (hW : W.transpose * W = 1)
    (hRW : R.transpose * W = 0) (hB : B.transpose * B = 1)
    (hBT : B.transpose * T = 0)
    (hWT : W*T = fun i j => (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) i (Fin.natAdd N j)) :
    ∃ V : Orthogonal N,
      (∀ lam : ι ⊕ Fin d → ℝ,
        ((U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose *
          (Matrix.fromCols R (W*B) * Matrix.diagonal lam * (Matrix.fromCols R (W*B)).transpose) *
          (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ)).submatrix (Fin.castAdd n) (Fin.castAdd n) =
          cavityConjugate V (Matrix.diagonal (fun j => lam (e.symm j)))) ∧
      cavityReservoirRows ((U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * (W*B)) =
        (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e := by
  let F := Matrix.fromCols R (W*B)
  let P := (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * F
  have hFG : F.transpose * F = 1 := cavityBaseFrame_gram R W B hR hW hRW hB
  have hPG : P.transpose * P = 1 := (cavityPhysicalFrame_gram U F).trans hFG
  have hPF : ∀ i : Fin n, ∀ j, P (Fin.natAdd N i) j = 0 := by
    apply cavityPhysicalFrame_lastRows _ F
    rw [← hWT]
    exact cavityBaseFrame_cavity_perp R W B T hW hRW hBT
  obtain ⟨V,hV⟩ := cavityReservoirRows_orthogonal e P hPG hPF
  refine ⟨V, ?_, ?_⟩
  · intro lam
    have hp : (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose *
        (F * Matrix.diagonal lam * F.transpose) * (U : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) =
        P * Matrix.diagonal lam * P.transpose := by
      simp only [P, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hp, cavityReservoirRows_conjugate]
    exact cavityReservoir_spectral_eq e P lam V hV
  · ext i j
    rw [cavityCanonicalSpecial_mul, hV]
    simp only [Equiv.symm_apply_apply]
    rfl

theorem cavityPhysicalBaseSpecial_simultaneous {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (U : Orthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g U)).transpose * B (cavityCompressionGrams g U) = 1)
    (hBT : (B (cavityCompressionGrams g U)).transpose *
      cavitySpectralStack (cavityCompressionGrams g U) = 0)
    (hA : ∀ a, (cavityCompressionGrams g U a).PosDef) :
    ∃ V : Orthogonal N,
      (∀ (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ),
        cavityPhysicalBase g lam B (Matrix.diagonal lam₀) U =
          cavityConjugate V (Matrix.diagonal
            (fun j => Sum.elim (fun w => lam w.1) lam₀ (e.symm j)))) ∧
      cavityPhysicalSpecial g B U =
        (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e := by
  classical
  let A := cavityColumns U
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
  have hWT : cavityEigenspaceFrame X * cavitySpectralStack (cavityCompressionGrams g U) = A := by
    change cavityEigenspaceFrame X * cavitySpectralStack (fun a => (X a).transpose * X a) = A
    rw [cavityEigenspaceFrame_stack X hA]
    exact cavitySpectralImage_sum g A
  obtain ⟨V, hV, hVS⟩ := cavityBaseFrame_simultaneous_orbit e U
    (cavityRetainedStack k R) (cavityEigenspaceFrame X) (B (cavityCompressionGrams g U))
    (cavitySpectralStack (cavityCompressionGrams g U))
    (cavityRetainedStack_gram k R hRG hcross)
    (cavityEigenspaceFrame_gram X hA (cavitySpectralImage_crossGram g A))
    (cavityRetainedStack_perp k R X hperp) hB hBT hWT
  refine ⟨V, ?_, hVS⟩
  intro lam lam₀
  have hJ := cavityBase_spectral_decomposition g A lam k R hRS hRP
    (B (cavityCompressionGrams g U)) (Matrix.diagonal lam₀)
  rw [← cavityBaseFrame_spectral_sum] at hJ
  change ((_ * cavityBaseReplacement _ _ _ _ _ * _).submatrix _ _) = _
  rw [hJ]
  exact hV (Sum.elim (fun w => lam w.1) lam₀)

end InvariantIsing

end

end OAI
