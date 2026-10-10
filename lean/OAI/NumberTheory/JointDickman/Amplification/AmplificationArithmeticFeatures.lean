import OAI.NumberTheory.JointDickman.Amplification.AmplificationBoxFeatures
import OAI.NumberTheory.JointDickman.Amplification.AmplificationDyadicIdentity

namespace OAI

/-! # The original amplification arithmetic sum has a bounded finite-feature kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def amplificationPrimeKernel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T : ℝ) :
    (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ :=
  polynomialPrimeKernel P m B j c H T (Real.log 2)
    (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T))
    (fun k => Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)

theorem amplification_arithmetic_feature_comparison
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
      ∀ U V : ℕ,
      (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
      (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*|amplificationArithmeticSum B j T U V g h-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*g x*h y*
            amplificationPrimeKernel P m B j c H T x y)| ≤ ε B+δ*(T/j)*singularSeries j ∧
        ∀ x y, |amplificationPrimeKernel P m B j c H T x y| ≤ C₀ := by
  intro δ hδ
  obtain ⟨P,c,hc,H,m,hm,C₀,hC₀,ε,hε,hcompare⟩ := amplification_box_feature_comparison
    hSD hSW hM hMP (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hη δ hδ
  refine ⟨P,c,hc,H,m,hm,C₀,hC₀,ε,hε,?_⟩
  filter_upwards [hcompare,eventually_ge_atTop 30] with B hb hB
  intro j _ Q hQ hscale hcut T hT hlogT hlag U V hU hV g h hg hh
  obtain ⟨_,hwindow,_⟩ := dyadic_scale_window hB hT hlogT
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  let s := fun k : ℤ => Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 30) hB)
  have hs : ∀ k ∈ S, |s k| ≤ 3 := by
    intro k hk
    rw [abs_le]
    constructor
    · apply (le_div_iff₀ hBpos).mpr
      nlinarith [(hwindow k hk).2.1]
    · apply (div_le_iff₀ hBpos).mpr
      nlinarith [(hwindow k hk).2.2]
  have he := hb j Q hQ hscale hcut T (lt_of_lt_of_le zero_lt_one hT) hlag S
    (fun k hk => (hwindow k hk).1) (fun k hk => (hwindow k hk).2) s hs g h hg hh
  rw [amplification_dyadic_identity hB hT hlogT j U V g h hU hV] at he
  exact he

end JointDickman

end OAI
