import OAI.NumberTheory.Ostmann.Tree.TwistedPairSpectrum

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem friendly_convolution_bound (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (hσ : (σ:ZMod p)^2=1) (hg0 : g 0=0) (hg : l2Sq g≤1)
    (hh0 : h 0=0) (hh : l2Sq h≤1)
    (η β : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ) :
    (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ∑ χ : MulChar (ZMod p) ℂ,
      ‖twistedPairFourier g σ χ (χ*η ψ) a‖^2 *
      ‖twistedPairFourier h τ ψ (β ψ) (-a)‖^2) ≤
      (2*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2)*
        ((correlationBound g:ℝ)^4+Real.sqrt (3/(p:ℝ))) := by
  let C : ℝ := ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*
        ((correlationBound g:ℝ)^4+Real.sqrt (3/(p:ℝ)))
  have hC : 0≤C := by dsimp [C]; positivity
  have hψ (ψ : MulChar (ZMod p) ℂ) :
      (∑ a : ZMod p, ∑ χ : MulChar (ZMod p) ℂ,
        ‖twistedPairFourier g σ χ (χ*η ψ) a‖^2 *
        ‖twistedPairFourier h τ ψ (β ψ) (-a)‖^2) ≤ C*pairFourthMass h ψ := by
    calc
      _ ≤ ∑ a : ZMod p, C*‖twistedPairFourier h τ ψ (β ψ) (-a)‖^2 := by
        apply Finset.sum_le_sum
        intro a _
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (twistedPairFourier_uniform g σ hσ hg0 hg (η ψ) a) (sq_nonneg _)
      _ = C*(∑ a : ZMod p, ‖twistedPairFourier h τ ψ (β ψ) a‖^2) := by
        rw [← Finset.mul_sum]
        congr 1
        exact (Equiv.neg (ZMod p)).bijective.sum_comp (fun a => ‖twistedPairFourier h τ ψ (β ψ) a‖^2)
      _ ≤ _ := mul_le_mul_of_nonneg_left (twistedPairFourier_energy h τ ψ (β ψ)) hC
  calc
    _ ≤ ∑ ψ : MulChar (ZMod p) ℂ, C*pairFourthMass h ψ := Finset.sum_le_sum (fun ψ _ => hψ ψ)
    _ = C*(∑ ψ : MulChar (ZMod p) ℂ,pairFourthMass h ψ) := by rw [Finset.mul_sum]
    _ ≤ C*(2*(p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)) := mul_le_mul_of_nonneg_left (pairFourthMass_total h hh0 hh) hC
    _ = _ := by dsimp [C]; ring

end
end Ostmann.FiniteField

end OAI
