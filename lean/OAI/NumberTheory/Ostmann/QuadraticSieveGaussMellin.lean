import OAI.NumberTheory.Ostmann.QuadraticSieveGaussMellinBasic

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

theorem gauss_mellin_divisor_range_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ), 0 < σ →
      ∀ (D N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ) (c : ℤ)
      (α : ℕ → ℕ → ℝ) (β γ : ℕ → ℝ) (H L : ℝ),
      0 < D → 0 < N → 0 < L → (∀ v ∈ V, Odd v) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, L ≤ (n : ℝ)) → (∀ t ∈ T, L ≤ (t : ℝ)) →
      (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ V, 0 < α d v) →
      (∀ n ∈ S, 0 < β n) → (∀ t ∈ T, 0 < γ t) →
      0 ≤ H → (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ V, (α d v)^(-σ) ≤ H) →
      ∃ p ∈ divisorRangeScales D,
        (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
          gaussMellinKernel a b c d v n t * ρ (α d v*β n*γ t)‖) ≤
          (1/(2*Real.pi))*(∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖)*H*(2/L)*
            Real.sqrt (C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
              quadraticNorm V (oddSquarefreeUpTo (N/p.1))*
              quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
              mellinWeightedEnergy S a β σ*mellinWeightedEnergy T b γ σ) := by
  obtain ⟨C,hC,hsep⟩ := gauss_product_divisor_range_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ρ σ hσ D N V S T a b c α β γ H L hD hN hL hV hS hT hSL hTL hα hβ hγ hH hαH
  obtain ⟨p,hp,hrow⟩ := hsep D N V S T L hD hN hL hV hS hT hSL hTL
  refine ⟨p,hp,?_⟩
  let E : ℝ := C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
    quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
    mellinWeightedEnergy S a β σ*mellinWeightedEnergy T b γ σ
  have hrow' (r : ℝ) : (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V,
      ‖gaussProductDivisorJacobiRow S T (mellinTwist σ r β a)
        (mellinTwist σ r γ b) c d (v : ℤ)‖) ≤ (2/L)*Real.sqrt E := by
    have h := hrow (mellinTwist σ r β a) (mellinTwist σ r γ b) c
    rw [coefficientEnergy_mellinTwist S a β σ r hβ,
      coefficientEnergy_mellinTwist T b γ σ r hγ] at h
    exact h
  have hweight (r : ℝ) : (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V, (α d v)^(-σ)*
      ‖gaussProductDivisorJacobiRow S T (mellinTwist σ r β a)
        (mellinTwist σ r γ b) c d (v : ℤ)‖) ≤ H*((2/L)*Real.sqrt E) := by
    calc
      _ ≤ ∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V, H*
          ‖gaussProductDivisorJacobiRow S T (mellinTwist σ r β a)
            (mellinTwist σ r γ b) c d (v : ℤ)‖ :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun v hv =>
          mul_le_mul_of_nonneg_right (hαH d hd v hv) (norm_nonneg _)))
      _ = H*∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V,
          ‖gaussProductDivisorJacobiRow S T (mellinTwist σ r β a)
            (mellinTwist σ r γ b) c d (v : ℤ)‖ := by simp_rw [←Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow' r) hH
  apply (gauss_range_mellin_separation (Finset.Ioc D (2*D)) V S T a b c
    ρ σ hσ α β γ hα hβ hγ).trans
  have hm := (Ostmann.schwartz_mellin_vertical_integrable ρ σ hσ).norm
  have hi := integral_mono
    (gauss_range_mellin_integrable (Finset.Ioc D (2*D)) V S T a b c
      ρ σ hσ α β γ hα hβ hγ)
    (hm.mul_const (H*((2/L)*Real.sqrt E)))
    (fun r => mul_le_mul_of_nonneg_left (hweight r) (norm_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ (1/(2*Real.pi) : ℝ) by positivity)
  rw [integral_mul_const] at hh
  convert hh using 1
  dsimp only [E]
  ring

end Ostmann.QuadraticSieve

end OAI
