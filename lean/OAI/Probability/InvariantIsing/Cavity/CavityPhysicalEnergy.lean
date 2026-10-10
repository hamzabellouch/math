import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticCompression
import OAI.Probability.InvariantIsing.Cavity.CavitySpecialPythagoras
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteIncrement

namespace OAI

/-! The exact original-spin energy difference is the finite random-block
cavity factor. All spectral-image and cavity-coordinate identities are
proved for the actual orthogonal matrix. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavity_physical_energy_difference {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (e : Fin (m*n) ≃ Fin (d+n))
    (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (σ : Spin N) (ε : Spin n) :
    let O := cavitySpecialOrthogonal U
    let B₁ := B (cavityCompressionGrams g O)
    let D := cavityRepeatedSpectrum (n := n) lam
    let T := cavitySpectralStack (cavityCompressionGrams g O)
    rotatedEnergy (fun i => lam (g i)) (specialRotation U) (cavityJoinedSpin (σ,ε)) -
      cavityQuadratic (cavityPhysicalBase g lam B (Matrix.diagonal lam₀) O)
        (fun i => spinValue (σ i)) =
      cavityLogFactor (B₁.transpose * D * B₁ - Matrix.diagonal lam₀)
        (B₁.transpose * D * T) (T.transpose * D * T)
        (cavityFullSpecialCoordinates g B₁ U (cavityJoinedSpin (σ,ε))).ofLp ε := by
  intro O B₁ D T
  let W := cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns O))
  let J := Matrix.diagonal (fun i => lam (g i))
  let R := cavityBaseReplacement J W D B₁ (Matrix.diagonal lam₀)
  let A := (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * R *
    (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ)
  let x := (specialRotation U (spinVector (cavityJoinedSpin (σ,ε)))).ofLp
  have hWG : W.transpose * W = 1 :=
    cavityEigenspaceFrame_gram _ hA (cavitySpectralImage_crossGram g (cavityColumns O))
  have hJW : J * W = W * D :=
    cavityEigenspaceFrame_eigen _ _ lam (cavitySpectralImage_eigen g (cavityColumns O) lam)
  have hWT : W * T = cavityColumns O :=
    (cavityEigenspaceFrame_stack _ hA).trans (cavitySpectralImage_sum g (cavityColumns O))
  have hT : T.transpose * T = 1 :=
    (cavitySpectralStack_gram _ (fun a => (hA a).posSemidef)).trans
      (cavityCompressionGrams_sum g O)
  have hcomplete : B₁ * B₁.transpose + T * T.transpose = 1 :=
    cavity_complement_projection_reindex e B₁ T hB hT hBT
  have hR : R.transpose = R :=
    cavityBaseReplacement_transpose J W D B₁ (Matrix.diagonal lam₀)
      (Matrix.diagonal_transpose _) (Matrix.diagonal_transpose _) (Matrix.diagonal_transpose _)
  have hAs : A.transpose = A := by
    simp only [A, Matrix.transpose_mul, Matrix.transpose_transpose, hR, Matrix.mul_assoc]
  have hRc : R * cavityColumns O = 0 := by
    rw [← hWT]
    exact cavityBaseReplacement_cavity J W D B₁ T _ hJW hWG hBT
  have hAc : ∀ i j, A i (Fin.natAdd N j) = 0 := by
    intro i j
    dsimp only [A]
    rw [Matrix.mul_assoc]
    change (∑ k, (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) k i *
      (R * cavityColumns O) k j) = 0
    rw [hRc]
    simp
  have hb := cavityQuadratic_first_block_of_symmetric A hAs hAc
    (fun i => spinValue (cavityJoinedSpin (σ,ε) i))
  have hx : x = (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) *ᵥ
      (fun i => spinValue (cavityJoinedSpin (σ,ε) i)) := rfl
  have hbase : cavityQuadratic R x =
      cavityQuadratic (cavityPhysicalBase g lam B (Matrix.diagonal lam₀) O)
        (fun i => spinValue (σ i)) := by
    rw [hx, ← cavityQuadratic_conjugate]
    simpa only [A, R, J, W, D, B₁, cavityPhysicalBase, cavityJoinedSpin,
      Fin.append_left] using hb
  have hcoord : (W * T).transpose *ᵥ x = fun j => spinValue (ε j) := by
    rw [hWT]
    simpa only [x, cavityJoinedSpin, spinVector_apply, Fin.append_right] using
      cavityColumns_transpose_rotation U (spinVector (cavityJoinedSpin (σ,ε)))
  have hdiff := cavityBaseReplacement_energy_difference J W D
    (Matrix.diagonal_transpose _) B₁ T hcomplete (Matrix.diagonal lam₀) x ε hcoord
  rw [hbase] at hdiff
  convert hdiff using 1
  · rw [cavityQuadratic_diagonal]
    rfl
  · rfl

end InvariantIsing

end

end OAI
