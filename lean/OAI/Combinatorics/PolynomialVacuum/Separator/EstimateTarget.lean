import OAI.Combinatorics.PolynomialVacuum.Pairing.PairingTarget
import OAI.Combinatorics.HoneycombCorridor.Bridges

namespace OAI

namespace PolynomialVacuumCylinder
open PolynomialVacuumBridge.Corridor

 
noncomputable def separatorExponent (s : ℂ) : ℝ :=
  1/6 + 2*(s^2).re/(3*Real.pi^2)

 

noncomputable def separatorLogCoefficient (n k : ℕ) : ℂ :=
  iteratedDeriv k (fun η : ℂ => Complex.log (separatorPolynomial n η)) 0 / (k.factorial : ℂ)

 

def NormalizedSeparatorPairing : Prop :=
  (∀ K : Set ℂ, IsCompact K →
    K ⊆ {s : ℂ | |s.im| < Real.pi} →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ s ∈ K,
      ‖separatorPolynomial n (2*Complex.cosh s)‖ ≤ C * (n : ℝ) ^ separatorExponent s) ∧
  (∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 1 ≤ n → ∀ η : ℂ,
    ‖η‖ < δ → separatorPolynomial n η ≠ 0) ∧
  (∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ‖separatorLogCoefficient n k‖ ≤ C*(1+Real.log (n : ℝ))) ∧
  Subpower (fun n => (separatorPolynomial n 2).re) (1/6)

end PolynomialVacuumCylinder

end OAI
