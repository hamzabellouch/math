import OAI.Probability.InvariantIsing.Cavity.CavitySpecialPythagoras
import OAI.Probability.InvariantIsing.Cavity.CavityConcreteFrameOrbit
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteIncrement

namespace OAI

/-! The full special coordinates are already coordinates of the base
spin: the special frame has zero rows at all cavity sites. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

theorem cavity_physical_special_coordinates {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (U : SpecialOrthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (σ : Spin N) (ε : Spin n) :
    (cavityFullSpecialCoordinates g
      (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
        (cavityJoinedSpin (σ,ε))).ofLp =
      (cavityPhysicalSpecial g B (cavitySpecialOrthogonal U)).transpose *ᵥ
        (fun i => spinValue (σ i)) := by
  let O := cavitySpecialOrthogonal U
  let W := cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns O))
  let B₁ := B (cavityCompressionGrams g O)
  let Q := (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ).transpose * (W * B₁)
  have hp : (cavityColumns O).transpose * (W * B₁) = 0 := by
    have h := cavityEigenspaceFrame_special_perp
      (cavitySpectralImage g (cavityColumns O)) hA
      (cavitySpectralImage_crossGram g (cavityColumns O)) B₁ hBT
    rw [cavitySpectralImage_sum] at h
    have ht := congrArg Matrix.transpose h
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using ht
  have hQ : ∀ i : Fin n, ∀ j, Q (Fin.natAdd N i) j = 0 :=
    cavityPhysicalFrame_lastRows (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) (W * B₁) hp
  have htrans : (W * B₁).transpose *
      (O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) = Q.transpose := by
    simp only [Q, Matrix.transpose_mul, Matrix.transpose_transpose]
  funext j
  change ((W * B₁).transpose *ᵥ
    ((O : Matrix (Fin (N+n)) (Fin (N+n)) ℝ) *ᵥ
      (fun i => spinValue (cavityJoinedSpin (σ,ε) i)))) j = _
  rw [Matrix.mulVec_mulVec, htrans]
  change (∑ i, Q i j * spinValue (cavityJoinedSpin (σ,ε) i)) =
    ∑ i, Q (Fin.castAdd n i) j * spinValue (σ i)
  simp only [Fin.sum_univ_add, hQ, zero_mul, Finset.sum_const_zero, add_zero,
    cavityJoinedSpin, Fin.append_left]

theorem cavity_coupled_special_coordinates {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (U : SpecialOrthogonal (N+n))
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (V : Orthogonal N) (S : Matrix (Fin N) (Fin d) ℝ)
    (hVS : cavityPhysicalSpecial g B (cavitySpecialOrthogonal U) =
      (V : Matrix (Fin N) (Fin N) ℝ) * S)
    (σ : Spin N) (ε : Spin n) :
    (cavityFullSpecialCoordinates g
      (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))) U
        (cavityJoinedSpin (σ,ε))).ofLp =
      S.transpose *ᵥ (matrixRotation V⁻¹ (spinVector σ)).ofLp := by
  rw [cavity_physical_special_coordinates g U B hBT hA σ ε, hVS,
    Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  rfl

end InvariantIsing

end

end OAI
