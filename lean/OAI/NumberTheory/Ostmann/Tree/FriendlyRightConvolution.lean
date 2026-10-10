import OAI.NumberTheory.Ostmann.Tree.FriendlyConvolution

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem friendly_convolution_right_bound (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (hτ : (τ:ZMod p)^2=1) (hg0 : g 0=0) (hg : l2Sq g≤1)
    (hh0 : h 0=0) (hh : l2Sq h≤1)
    (α η : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ∑ ψ : MulChar (ZMod p) ℂ,
      ‖twistedPairFourier g σ χ (α χ) a‖^2 *
      ‖twistedPairFourier h τ ψ (ψ*η χ) (-a)‖^2) ≤
      (2*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2)*
        ((correlationBound h:ℝ)^4+Real.sqrt (3/(p:ℝ))) := by
  have he : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ∑ ψ : MulChar (ZMod p) ℂ,
      ‖twistedPairFourier g σ χ (α χ) a‖^2 *
      ‖twistedPairFourier h τ ψ (ψ*η χ) (-a)‖^2) =
      ∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ∑ ψ : MulChar (ZMod p) ℂ,
      ‖twistedPairFourier h τ ψ (ψ*η χ) a‖^2 *
      ‖twistedPairFourier g σ χ (α χ) (-a)‖^2 := by
    apply Finset.sum_congr rfl
    intro χ _
    have hi := (Equiv.neg (ZMod p)).bijective.sum_comp
      (fun a => ∑ ψ : MulChar (ZMod p) ℂ,
        ‖twistedPairFourier h τ ψ (ψ*η χ) a‖^2 *‖twistedPairFourier g σ χ (α χ) (-a)‖^2)
    simpa only [Equiv.neg_apply,neg_neg,mul_comm] using hi
  rw [he]
  exact friendly_convolution_bound h g τ σ hτ hh0 hh hg0 hg η α

end
end Ostmann.FiniteField

end OAI
