import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalEnergy
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalCoordinates

namespace OAI

/-! The physical energy identity expressed in the coupled base eigenbasis
and the same special axes that appear in the Haar comparison. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

theorem cavity_coupled_energy_difference {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (e : Fin (m*n) ≃ Fin (d+n))
    (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (V : Orthogonal N) (eig₀ : Fin N → ℝ) (S : Matrix (Fin N) (Fin d) ℝ)
    (hV : cavityPhysicalBase g lam B (Matrix.diagonal lam₀) (cavitySpecialOrthogonal U) =
      (V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal eig₀ *
        (V : Matrix (Fin N) (Fin N) ℝ).transpose)
    (hVS : cavityPhysicalSpecial g B (cavitySpecialOrthogonal U) =
      (V : Matrix (Fin N) (Fin N) ℝ) * S)
    (σ : Spin N) (ε : Spin n) :
    let B₁ := B (cavityCompressionGrams g (cavitySpecialOrthogonal U))
    let D := cavityRepeatedSpectrum (n := n) lam
    let T := cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U))
    rotatedEnergy (fun i => lam (g i)) (specialRotation U) (cavityJoinedSpin (σ,ε)) -
      rotatedEnergy eig₀ (matrixRotation V⁻¹) σ =
      cavityLogFactor (B₁.transpose * D * B₁ - Matrix.diagonal lam₀)
        (B₁.transpose * D * T) (T.transpose * D * T)
        (S.transpose *ᵥ (matrixRotation V⁻¹ (spinVector σ)).ofLp) ε := by
  have h := cavity_physical_energy_difference g e U lam lam₀ B hB hBT hA σ ε
  dsimp only at h ⊢
  rw [hV, cavityQuadratic_inverse_rotation,
    cavity_coupled_special_coordinates g U B hBT hA V S hVS σ ε] at h
  exact h

end InvariantIsing

end

end OAI
