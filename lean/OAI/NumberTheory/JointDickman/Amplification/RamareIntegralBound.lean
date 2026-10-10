import OAI.NumberTheory.JointDickman.Amplification.RamareProductIntegral
import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryLargeSamples

namespace OAI

/-! # The prime/cofactor integral with auxiliary large values discharged -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem ramare_product_integral_bound (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in atTop,
      ∀ (N : ℕ) (P Q : Finset ℕ) (F f : ℕ → ℂ),
      1 ≤ a → 2 ≤ (N:ℝ)/a → OneBounded F → OneBounded f →
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ (E : Set ℝ) (T b K : ℝ), MeasurableSet E → 0 ≤ T →
      E ⊆ Set.Ioc (-T) T → 2*T ≤ a^B →
      (∀ U : Finset ℝ, (∀ t ∈ U, t ∈ E) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) → (U.card:ℝ) ≤ K) →
      (∀ t ∈ E, ‖mrtCofactorPolynomial P F N a t‖ ≤ b) →
      (∫ t in E, ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ)) t*mrtCofactorPolynomial P F N a t‖^2) ≤
        2*((((Real.log a)^10)⁻¹)^2*
          (48000*(2*(1+Real.log (2*T+1))+K*Real.sqrt (2*T)*a/N))+
          b^2*(C/(Real.log a)^2)) := by
  obtain ⟨C,γ,hC,hγ,hbound⟩ := ramare_product_sparse_integral B hB
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,auxiliary_large_samples B hB hγ] with a haBound haLarge
  intro N P Q F f ha hx hF hf hQ E T b K hEm hT hET hTB hcard hb
  apply haBound N P Q F f ha hx hF hf hQ E T (((Real.log a)^10)⁻¹) b K
    hEm hT (by positivity) hET hTB
  · intro U hUE hsep
    refine ⟨hcard U hUE hsep,?_⟩
    apply haLarge Q hQ f hf U hsep
    intro t ht
    obtain ⟨hlo,hhi⟩ := hET (hUE t ht)
    have htT : |t| ≤ T := abs_le.mpr ⟨by linarith,by linarith⟩
    exact htT.trans (by linarith)
  · intro t ht _
    exact hb t ht

end JointDickman

end OAI
