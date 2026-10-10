import OAI.NumberTheory.Ostmann.Tree.CrossedMoments
import OAI.NumberTheory.Ostmann.Tree.SpectralParts

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem bad_nonprincipal_convolution_bound (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (ν : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1)
    (hh0 : h 0=0) (hh : l2Sq h≤1) :
    (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      nonprincipalEnergy g σ χ (ν*ψ⁻¹) a*
      nonprincipalEnergy h τ ψ (ν⁻¹*χ⁻¹) (-a)) ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^3*
        (2*(correlationBound g:ℝ)^2+2*(correlationBound h:ℝ)^2+3/(p:ℝ)) := by
  have hc := crossed_moment_bound (nonprincipalEnergy g σ) (nonprincipalEnergy h τ)
    ν (Equiv.neg (ZMod p))
  change 2*(∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      nonprincipalEnergy g σ χ (ν*ψ⁻¹) a*nonprincipalEnergy h τ ψ (ν⁻¹*χ⁻¹) (-a)) ≤ _ at hc
  have hL := nonprincipalEnergy_fourth g σ hg0 hg
  have hR := nonprincipalEnergy_fourth h τ hh0 hh
  nlinarith only [hc,hL,hR]

end
end Ostmann.FiniteField

end OAI
