import OAI.NumberTheory.CubicGram.SieveImprovement
import OAI.NumberTheory.CubicGram.FullCubeExtraction

namespace OAI

/-! Quantitative cubic-sieve bounds on the actual decomposed frequencies.
The residual factor includes the ramified part; the cube variable causes only
an exclusion and therefore costs its cardinality. No exceptional-moment
estimate is assumed here. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- Both orientations of the published cubic large sieve on a frequency
block `r*p*q²*j³`, with the cube and ramified multiplicities explicit. -/
theorem residualFrequency_sieve_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (B R P Q J : Finset Eisenstein) (N U V : ℝ),
      1 ≤ N → 1 ≤ U → 1 ≤ V →
      (∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ U) →
      (∀ q ∈ Q, primary q ∧ Squarefree q ∧ norm q ≤ V) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ residualCubeSupport R P Q J, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
        (R.card:ℝ)*J.card*C₀ *
          min ((Q.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)))
              ((P.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))) *
            ∑ b ∈ B, ‖β b‖^2 := by
  intro ε hε
  obtain ⟨C₀,hC,hsharp⟩ := finiteCubicBound_sharp ε hε
  refine ⟨C₀,hC,?_⟩
  intro B R P Q J N U V hN hU hV hB hP hQ β
  have hp := hsharp B P U N hU hN hB hP
  have hq := hsharp B Q V N hV hN hB hQ
  apply (residualCubeSupport_mass_le B R P Q J (fun b hb => (hB b hb).1) β).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc
    _ ≤ (R.card:ℝ) *
        min ((Q.card:ℝ)*J.card*(C₀*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ))))
            ((P.card:ℝ)*J.card*(C₀*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact min_le_min (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_le_mul_of_nonneg_left hq (by positivity))
    _ = _ := by
      have h₁ : (Q.card:ℝ)*J.card*(C₀*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ))) =
          (J.card:ℝ)*C₀*((Q.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ))) := by ring
      have h₂ : (P.card:ℝ)*J.card*(C₀*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))) =
          (J.card:ℝ)*C₀*((P.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))) := by ring
      rw [h₁,h₂,← mul_min_of_nonneg _ _ (by positivity : 0 ≤ (J.card:ℝ)*C₀)]
      ring

/-- Restricting the actual frequencies, for instance to noncubes and a norm
dyad, can only decrease the positive quadratic mass. -/
theorem frequency_subset_mass_le (H F B : Finset Eisenstein)
    (hHF : H ⊆ F) (β : Eisenstein → ℂ) :
    (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
      ∑ h ∈ F, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2 :=
  Finset.sum_le_sum_of_subset_of_nonneg hHF (fun _ _ _ => sq_nonneg _)

/-- A fixed norm or angular phase, or a fixed arithmetic exclusion, is
absorbed into the coefficients without increasing their squared norm. -/
theorem twisted_residualFrequency_sieve_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (B R P Q J H : Finset Eisenstein) (N U V : ℝ),
      1 ≤ N → 1 ≤ U → 1 ≤ V →
      (∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ U) →
      (∀ q ∈ Q, primary q ∧ Squarefree q ∧ norm q ≤ V) →
      H ⊆ residualCubeSupport R P Q J →
      ∀ β z : Eisenstein → ℂ, (∀ b ∈ B, ‖z b‖ ≤ 1) →
      (∑ h ∈ H, ‖∑ b ∈ B, β b*z b*cubicSymbol b h‖^2) ≤
        (R.card:ℝ)*J.card*C₀ *
          min ((Q.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)))
              ((P.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))) *
            ∑ b ∈ B, ‖β b‖^2 := by
  intro ε hε
  obtain ⟨C₀,hC,hbound⟩ := residualFrequency_sieve_bound ε hε
  refine ⟨C₀,hC,?_⟩
  intro B R P Q J H N U V hN hU hV hB hP hQ hH β z hz
  apply (frequency_subset_mass_le H _ B hH (fun b => β b*z b)).trans
  apply (hbound B R P Q J N U V hN hU hV hB hP hQ (fun b => β b*z b)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul,mul_pow]
  exact mul_le_of_le_one_right (sq_nonneg _) (by
    simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (hz b hb) 2)

end CubicFirstMoment

end

end OAI
