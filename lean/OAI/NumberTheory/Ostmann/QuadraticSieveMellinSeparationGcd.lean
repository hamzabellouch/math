import OAI.NumberTheory.Ostmann.QuadraticSieveMellinSeparationSelection

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

theorem coprime_jacobi_mellin_gcd_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ), 0 < σ →
      ∀ (V S T : Finset ℕ) (a b : ℕ → ℂ) (d N : ℕ) (α β γ : ℕ → ℝ) (H : ℝ),
      d ≠ 0 → (∀ v ∈ V, Odd v) → S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∀ v ∈ V, 0 < α v) → (∀ n ∈ S, 0 < β n) → (∀ t ∈ T, 0 < γ t) →
      0 ≤ H → (∀ v ∈ V, (α v) ^ (-σ) ≤ H) →
      ∃ d₁ d₂ : ℕ, 0 < d₁ ∧ 0 < d₂ ∧ d₁ * d₂ = d ∧
        (∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
          if n.Coprime t ∧ d ∣ n * t then
            a n * b t * (jacobiSym (v : ℤ) (n * t) : ℂ) * ρ (α v * β n * γ t) else 0‖) ≤
          (1 / (2 * Real.pi)) * (∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖) * H *
            Real.sqrt (C * (N : ℝ) ^ ε * quadraticNorm V (oddSquarefreeUpTo (N / d₁)) *
              quadraticNorm V (oddSquarefreeUpTo (N / d₂)) *
              mellinWeightedEnergy S a β σ * mellinWeightedEnergy T b γ σ) := by
  obtain ⟨C, hC, hsep⟩ := exists_uniform_mellin_gcd_scales ε hε
  refine ⟨C, hC, ?_⟩
  intro ρ σ hσ V S T a b d N α β γ H hd hV hS hT hα hβ hγ hH hαH
  obtain ⟨d₁, d₂, hd₁, hd₂, hprod, hrow⟩ :=
    hsep V S T a b d N β γ σ hd hV hS hT hβ hγ
  refine ⟨d₁, d₂, hd₁, hd₂, hprod, ?_⟩
  let E := C * (N : ℝ) ^ ε * quadraticNorm V (oddSquarefreeUpTo (N / d₁)) *
    quadraticNorm V (oddSquarefreeUpTo (N / d₂)) *
    mellinWeightedEnergy S a β σ * mellinWeightedEnergy T b γ σ
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (quadraticNorm_nonneg _ _)) (quadraticNorm_nonneg _ _))
      (mellinWeightedEnergy_nonneg _ _ _ _)) (mellinWeightedEnergy_nonneg _ _ _ _)
  have hrow' (r : ℝ) : (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T
      (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖) ≤ Real.sqrt E := by
    have h := hrow r
    change _ ≤ E at h
    have hn : 0 ≤ ∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T
      (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg E]
  have hweight (r : ℝ) : (∑ v ∈ V, (α v) ^ (-σ) *
      ‖coprimeProductDivisorJacobiRow S T
        (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖) ≤ H * Real.sqrt E := by
    calc
      _ ≤ ∑ v ∈ V, H * ‖coprimeProductDivisorJacobiRow S T
          (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖ :=
        Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_right (hαH v hv) (norm_nonneg _))
      _ = H * ∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T
          (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖ :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow' r) hH
  apply (coprime_jacobi_mellin_separation V S T a b d ρ σ hσ α β γ hα hβ hγ).trans
  have hm := (Ostmann.schwartz_mellin_vertical_integrable ρ σ hσ).norm
  have hi := integral_mono
    (coprime_jacobi_mellin_weight_integrable V S T a b d ρ σ hσ α β γ hα hβ hγ)
    (hm.mul_const (H * Real.sqrt E))
    (fun r => mul_le_mul_of_nonneg_left (hweight r) (norm_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ (1 / (2 * Real.pi) : ℝ) by positivity)
  rw [integral_mul_const] at hh
  convert hh using 1
  dsimp [E]
  ring

end Ostmann.QuadraticSieve

end OAI
