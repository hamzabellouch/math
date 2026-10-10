import OAI.NumberTheory.JointDickman.Amplification.CanonicalExceptionalSamples
import OAI.NumberTheory.JointDickman.Amplification.RamareIntegralBound

namespace OAI

/-! # Auxiliary prime products on the actual exceptional frequency set -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem exceptional_product_integral (P₀ Q₀ B : ℝ)
    (hP : 2*Real.exp 1 ≤ P₀) (hPQ : P₀ ≤ Q₀)
    (hlogP : 1 ≤ Real.log P₀) (hQ : 1 ≤ Real.log Q₀)
    (hH : 2 ≤ mrtBaseResolution P₀ Q₀ (1/12)) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in atTop, ∀ᶠ X : ℝ in atTop,
      let J := mellinBandCount Q₀ (Real.sqrt (Real.log X)) hQ
      let D := canonicalMellinBands P₀ Q₀ (1/12)
      ∀ (N : ℕ) (P Q : Finset ℕ) (F f g : ℕ → ℂ),
      1 ≤ a → 2 ≤ (N:ℝ)/a → OneBounded F → OneBounded f → OneBounded g →
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ (E : Set ℝ) (T b : ℝ), MeasurableSet E → 0 ≤ T → T ≤ X →
      E ⊆ Set.Ioc (-T) T →
      E ⊆ mrtNoSmallBand D.bins (D.polynomial g) D.threshold J →
      2*T ≤ a^B → (∀ t ∈ E, ‖mrtCofactorPolynomial P F N a t‖ ≤ b) →
      (∫ t in E, ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ)) t*mrtCofactorPolynomial P F N a t‖^2) ≤
        2*((((Real.log a)^10)⁻¹)^2*
          (48000*(2*(1+Real.log (2*T+1))+
            ((mrtBaseResolution P₀ Q₀ (1/12)*(Real.log X)^2+1)*X^(5/12:ℝ))*
              Real.sqrt (2*T)*a/N))+b^2*(C/(Real.log a)^2)) := by
  obtain ⟨C,hC,hbound⟩ := ramare_product_integral_bound B hB
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with a haBound
  filter_upwards [canonical_exceptional_samples P₀ Q₀ hP hPQ hlogP hQ hH] with X hX
  dsimp only at hX ⊢
  intro N P Q F f g ha hx hF hf hg hpr E T b hEm hT hTX hET hEres hTB hb
  apply haBound N P Q F f ha hx hF hf hpr E T b
    ((mrtBaseResolution P₀ Q₀ (1/12)*(Real.log X)^2+1)*X^(5/12:ℝ)) hEm hT hET hTB
  · intro U hUE hsep
    refine hX g hg U ?_ hsep ?_
    · intro t ht
      obtain ⟨hlo,hhi⟩ := hET (hUE t ht)
      exact (abs_le.mpr ⟨by linarith,by linarith⟩).trans hTX
    · intro t ht
      exact hEres (hUE t ht)
  · exact hb

end JointDickman

end OAI
