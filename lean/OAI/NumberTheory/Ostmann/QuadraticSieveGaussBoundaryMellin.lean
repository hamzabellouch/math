import OAI.NumberTheory.Ostmann.QuadraticSieveGaussBoundary
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussMellinBasic

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

theorem gauss_mellin_boundary_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ), 0 < σ →
      ∀ (N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ) (c : ℤ)
      (α β γ : ℕ → ℝ) (H L : ℝ),
      0 < N → 0 < L → (∀ v ∈ V, Odd v) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, L ≤ (n : ℝ)) → (∀ t ∈ T, L ≤ (t : ℝ)) →
      (∀ v ∈ V, 0 < α v) → (∀ n ∈ S, 0 < β n) → (∀ t ∈ T, 0 < γ t) →
      0 ≤ H → (∀ v ∈ V, (α v)^(-σ) ≤ H) →
      (∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
        gaussMellinKernel a b c 1 v n t * ρ (α v*β n*γ t)‖) ≤
        (1/(2*Real.pi))*(∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖)*H*(2/L)*
          Real.sqrt (C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2*
            mellinWeightedEnergy S a β σ*mellinWeightedEnergy T b γ σ) := by
  obtain ⟨C,hC,hsep⟩ := gauss_product_boundary_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ρ σ hσ N V S T a b c α β γ H L hN hL hV hS hT hSL hTL hα hβ hγ hH hαH
  have hrow := hsep N V S T L hN hL hV hS hT hSL hTL
  let E : ℝ := C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2*
    mellinWeightedEnergy S a β σ*mellinWeightedEnergy T b γ σ
  have hrow' (r : ℝ) : (∑ v ∈ V,
      ‖gaussProductDivisorJacobiRow S T (mellinTwist σ r β a)
        (mellinTwist σ r γ b) c 1 (v : ℤ)‖) ≤ (2/L)*Real.sqrt E := by
    have hh := hrow (mellinTwist σ r β a) (mellinTwist σ r γ b) c
    rw [coefficientEnergy_mellinTwist S a β σ r hβ,
      coefficientEnergy_mellinTwist T b γ σ r hγ] at hh
    exact hh
  have hweight (r : ℝ) : (∑ v ∈ V, (α v)^(-σ)*
      ‖gaussProductDivisorJacobiRow S T (mellinTwist σ r β a)
        (mellinTwist σ r γ b) c 1 (v : ℤ)‖) ≤ H*((2/L)*Real.sqrt E) := by
    calc
      _ ≤ ∑ v ∈ V, H*‖gaussProductDivisorJacobiRow S T (mellinTwist σ r β a)
          (mellinTwist σ r γ b) c 1 (v : ℤ)‖ :=
        Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_right (hαH v hv) (norm_nonneg _))
      _ = H*∑ v ∈ V, ‖gaussProductDivisorJacobiRow S T (mellinTwist σ r β a)
          (mellinTwist σ r γ b) c 1 (v : ℤ)‖ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow' r) hH
  have hs := gauss_range_mellin_separation {1} V S T a b c ρ σ hσ (fun _ v => α v) β γ
    (fun _ _ v hv => hα v hv) hβ hγ
  simp only [Finset.sum_singleton] at hs
  apply hs.trans
  have hm := (Ostmann.schwartz_mellin_vertical_integrable ρ σ hσ).norm
  have hg := gauss_range_mellin_integrable {1} V S T a b c ρ σ hσ (fun _ v => α v) β γ
    (fun _ _ v hv => hα v hv) hβ hγ
  simp only [Finset.sum_singleton] at hg
  have hi := integral_mono hg (hm.mul_const (H*((2/L)*Real.sqrt E)))
    (fun r => mul_le_mul_of_nonneg_left (hweight r) (norm_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ (1/(2*Real.pi) : ℝ) by positivity)
  rw [integral_mul_const] at hh
  convert hh using 1
  dsimp only [E]
  ring

end Ostmann.QuadraticSieve

end OAI
