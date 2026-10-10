import OAI.NumberTheory.JointDickman.Probability.AmplificationFairKernel
import OAI.NumberTheory.JointDickman.Amplification.AmplificationArithmeticFeatures

namespace OAI

/-! # The conditional finite-feature comparison for the actual split kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_fair_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {η : ℝ} (hη : 0 < η) :
    ∀ δ : ℝ, 0 < δ → ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ H m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j →
      ∀ V : ℕ,
      (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*|(∑ x : auxiliaryPrimes B → Bool, ∑ y : auxiliaryPrimes B → Bool,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*g x*h y*
            amplificationFairKernel B j T V x y)-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*g x*h y*
            amplificationPrimeKernel P m B j c H T x y)| ≤ ε B+δ*(T/j)*singularSeries j ∧
        ∀ x y, |amplificationPrimeKernel P m B j c H T x y| ≤ C₀ := by
  intro δ hδ
  obtain ⟨P,c,hc,H,m,hm,C₀,hC₀,ε,hε,hcompare⟩ :=
    amplification_arithmetic_feature_comparison hSD hSW hM hMP hη δ hδ
  refine ⟨P,c,hc,H,m,hm,C₀,hC₀,ε,hε,?_⟩
  filter_upwards [hcompare] with B hB
  intro j _ Q hQ hscale hcut T hT hlogT hlag V hV g h hg hh
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  let f : ℤ → ℕ := fun k => ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊
  let U := max (∏ p ∈ auxiliaryPrimes B,p) (S.sup f)
  have hprod : (∏ p ∈ auxiliaryPrimes B,p) ≤ U := le_max_left _ _
  have hU : ∀ k ∈ S, f k ≤ U := fun k hk =>
    (le_sup (f := f) hk).trans (le_max_right _ _)
  have he := hB j Q hQ hscale hcut T hT hlogT hlag U V hU hV g h hg hh
  rw [amplificationArithmeticSum_eq_fairKernel B j T U V hprod g h] at he
  exact he

end JointDickman

end OAI
