import OAI.InformationTheory.SecretKey.Model
import OAI.InformationTheory.DimensionTen.StateDensity

namespace OAI

/-! The normalized Choi state and key separation in the finite terminal-readout model. -/

noncomputable section
open Matrix

namespace ZeroKey.TenDimensional

universe u

def rho : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ :=
  DimensionTen.rho

def MainClaim : Prop :=
  ∃ hR : Density rho, ¬ Separable rho ∧
    (∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
      rho *ᵥ w = DimensionTen.productVector u v → u = 0 ∨ v = 0) ∧
    distillableSecretKey.{u} rho hR = 0 ∧
    UniformProtocolGap.{u} rho hR ∧ UniformCompletedGap.{u} rho hR

end ZeroKey.TenDimensional

end

end OAI
