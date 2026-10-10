import OAI.NumberTheory.JointDickman.Amplification.WeightedArithmeticFeatures
import OAI.NumberTheory.JointDickman.Probability.TensorCutoff

namespace OAI

/-! # The weighted arithmetic comparison for compact Schwartz factors -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem schwartz_arithmetic_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η) (hR : 0 ≤ R)
    (w₁ w₂ w : 𝓢(ℝ,ℝ))
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hs₃ : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => r k*coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)
      T*|weightedGeometricArithmeticSum B j a b l u T t S r g h w₁ w₂ w-
        (singularSeries j/(j : ℝ))*
          (∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
            g x*h y*primeCoarseKernel m B K x y)| ≤
        ε B+δ*(T/j)*singularSeries j := by
  obtain ⟨M₁,D₁,hM₁,hD₁,hv₁,hd₁,_⟩ := schwartz_value_derivative_bounds w₁
  obtain ⟨M₂,D₂,hM₂,hD₂,hv₂,hd₂,_⟩ := schwartz_value_derivative_bounds w₂
  obtain ⟨M₀,D₀,hM₀,hD₀,hv₀,hd₀,hc₀⟩ := schwartz_value_derivative_bounds w
  exact weighted_geometric_arithmetic_feature_comparison hSD hSW hM hMP
    ha hab hl hlu ht hη w₁ w₂ (deriv w₁) (deriv w₂) w (deriv w) hR
    (add_nonneg hM₁ hM₂) hD₁ hD₂ hM₀ hD₀ w₁.hasDerivAt w₂.hasDerivAt
    (fun x => (hv₁ x).trans (le_add_of_nonneg_right hM₂))
    (fun x => (hv₂ x).trans (le_add_of_nonneg_left hM₁)) hd₁ hd₂ hs₁ hs₂
    w.hasDerivAt hc₀ hv₀ hd₀ hs₃

end JointDickman

end OAI
