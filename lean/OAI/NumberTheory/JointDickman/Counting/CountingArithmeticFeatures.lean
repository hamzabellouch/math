import OAI.NumberTheory.JointDickman.Counting.CountingDyadicIdentity

namespace OAI

/-! # The original amplification arithmetic sum has a bounded finite-feature kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def countingPrimeKernel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ) :
    (auxiliaryPrimes B → Bool) → (auxiliaryPrimes B → Bool) → ℝ :=
  weightedPolynomialPrimeKernel P m B j c H T (Real.log 2)
    (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T))
    (fun _ => σ)
    (fun k => amplificationBump (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B))

theorem counting_arithmetic_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {η w : ℝ} (hη : 0 < η) (hw : 0 < w) :
    ∀ δ : ℝ, 0 < δ → ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ H m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j →
      ∀ σ : ℝ, |σ| ≤ 3 →
      ∀ U V : ℕ,
      (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
      (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*|rampedAmplificationArithmeticSum B j T U V w σ g h-
        (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
          fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*g x*h y*
            countingPrimeKernel P m B j c H T σ x y)| ≤ ε B+δ*(T/j)*singularSeries j ∧
        ∀ x y, |countingPrimeKernel P m B j c H T σ x y| ≤ C₀ := by
  intro δ hδ
  obtain ⟨P,c,hc,H,m,hm,C₀,hC₀,ε,hε,hcompare⟩ := counting_box_feature_comparison
    hSD hSW hM hMP (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hη hw δ hδ
  refine ⟨P,c,hc,H,m,hm,C₀,hC₀,ε,hε,?_⟩
  filter_upwards [hcompare,eventually_ge_atTop 30] with B hb hB
  intro j _ Q hQ hscale hcut T hT hlogT hlag σ hσ U V hU hV g h hg hh
  obtain ⟨_,hwindow,_⟩ := dyadic_scale_window hB hT hlogT
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  let s := fun k : ℤ => Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B
  have he := hb j Q hQ hscale hcut T (lt_of_lt_of_le zero_lt_one hT) hlag S
    (fun k hk => (hwindow k hk).1) (fun k hk => (hwindow k hk).2) s (fun _ => σ)
    (fun _ _ => hσ) g h hg hh
  rw [counting_dyadic_identity hB hT hlogT j U V w σ g h hU hV] at he
  exact he

end JointDickman

end OAI
