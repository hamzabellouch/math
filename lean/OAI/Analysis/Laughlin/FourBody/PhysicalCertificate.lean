import OAI.Analysis.Laughlin.FourBody.PhysicalGram
import OAI.Analysis.Laughlin.FourBody.ScaledAll

namespace OAI

namespace Laughlin.Fock
open scoped Matrix

noncomputable def physicalLimitGram (Q D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ :=
  fun i j => (occupationInner Q (limitFourColumn Q (Certificate.copyLabel i) D)
    (limitFourColumn Q (Certificate.copyLabel j) D)).re

noncomputable def physicalLimitError (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ :=
  fun i j => Spin.limitFourError D (Certificate.copyLabel i) (Certificate.copyLabel j)

theorem physicalLimitGram_eq (Q D : ℕ) (hQ : D+1 ≤ Q) :
    physicalLimitGram Q D = Certificate.scaledGram D := by
  ext i j
  simp [physicalLimitGram,source_fourBody_physical_scaledGram Q D hQ]

theorem physicalLimitError_eq (D : ℕ) : physicalLimitError D = Certificate.scaledError D := by
  ext i j
  exact Spin.source_fourBody_error_matrix D i j

theorem source_physical_four_body_certificates (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (physicalLimitGram Q D * (Certificate.certificateDiagonal D-physicalLimitError D) *
      physicalLimitGram Q D).PosSemidef := by
  rw [physicalLimitGram_eq Q D hQ,physicalLimitError_eq]
  exact Certificate.scaled_four_body_certificates D hD₁ hD₂

end Laughlin.Fock

end OAI
