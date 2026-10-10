import OAI.NumberTheory.Ostmann.QuadraticSieveMellinDivisorRangesSelection

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

theorem coprime_jacobi_range_mellin_separation (D V S T : Finset ℕ) (a b : ℕ → ℂ)
    (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) (α : ℕ → ℕ → ℝ) (β γ : ℕ → ℝ)
    (hα : ∀ d ∈ D, ∀ v ∈ V, 0 < α d v)
    (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    (∑ d ∈ D, ∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
      if n.Coprime t ∧ d ∣ n * t then
        a n * b t * (jacobiSym (v : ℤ) (n * t) : ℂ) * ρ (α d v * β n * γ t) else 0‖) ≤
      (1 / (2 * Real.pi)) * (∫ r : ℝ,
        ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖ *
          ∑ d ∈ D, ∑ v ∈ V, (α d v) ^ (-σ) *
            ‖coprimeProductDivisorJacobiRow S T
              (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖) := by
  have h := finite_bilinear_mellin_separation (D ×ˢ V) S T ρ σ hσ
    (fun p => coprimeMellinJacobiKernel a b p.1 p.2) (fun p => α p.1 p.2) β γ
    (fun p hp => hα p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) hβ hγ
  simp_rw [bilinearMellinRow_jacobi] at h
  simpa only [Finset.sum_product, coprimeMellinJacobiKernel, ite_mul, zero_mul] using h

theorem coprime_jacobi_range_mellin_integrable (D V S T : Finset ℕ) (a b : ℕ → ℂ)
    (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) (α : ℕ → ℕ → ℝ) (β γ : ℕ → ℝ)
    (hα : ∀ d ∈ D, ∀ v ∈ V, 0 < α d v)
    (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    Integrable (fun r : ℝ => ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖ *
      ∑ d ∈ D, ∑ v ∈ V, (α d v) ^ (-σ) *
        ‖coprimeProductDivisorJacobiRow S T
          (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖) := by
  have h := finite_bilinear_mellin_weight_integrable (D ×ˢ V) S T ρ σ hσ
    (fun p => coprimeMellinJacobiKernel a b p.1 p.2) (fun p => α p.1 p.2) β γ
    (fun p hp => hα p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) hβ hγ
  simpa only [Finset.sum_product, bilinearMellinRow_jacobi] using h

theorem coprime_jacobi_mellin_divisor_range_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ), 0 < σ →
      ∀ (D N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ)
      (α : ℕ → ℕ → ℝ) (β γ : ℕ → ℝ) (H : ℝ),
      0 < D → 0 < N → (∀ v ∈ V, Odd v) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∀ d ∈ Finset.Ioc D (2 * D), ∀ v ∈ V, 0 < α d v) →
      (∀ n ∈ S, 0 < β n) → (∀ t ∈ T, 0 < γ t) →
      0 ≤ H → (∀ d ∈ Finset.Ioc D (2 * D), ∀ v ∈ V, (α d v) ^ (-σ) ≤ H) →
      ∃ p ∈ divisorRangeScales D,
        (∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
          if n.Coprime t ∧ d ∣ n * t then
            a n * b t * (jacobiSym (v : ℤ) (n * t) : ℂ) * ρ (α d v * β n * γ t) else 0‖) ≤
          (1 / (2 * Real.pi)) * (∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖) * H *
            Real.sqrt (C * (N : ℝ) ^ ε * (p.1 * p.2 : ℕ) *
              quadraticNorm V (oddSquarefreeUpTo (N / p.1)) *
              quadraticNorm V (oddSquarefreeUpTo (N / p.2)) *
              mellinWeightedEnergy S a β σ * mellinWeightedEnergy T b γ σ) := by
  obtain ⟨C,hC,hsep⟩ := exists_uniform_mellin_divisor_scales ε hε
  refine ⟨C,hC,?_⟩
  intro ρ σ hσ D N V S T a b α β γ H hD hN hV hS hT hα hβ hγ hH hαH
  obtain ⟨p,hp,hrow⟩ := hsep D N V S T a b β γ σ hD hN hV hS hT hβ hγ
  refine ⟨p,hp,?_⟩
  let E := C * (N : ℝ) ^ ε * (p.1 * p.2 : ℕ) *
    quadraticNorm V (oddSquarefreeUpTo (N / p.1)) *
    quadraticNorm V (oddSquarefreeUpTo (N / p.2)) *
    mellinWeightedEnergy S a β σ * mellinWeightedEnergy T b γ σ
  have hQA := quadraticNorm_nonneg V (oddSquarefreeUpTo (N / p.1))
  have hQB := quadraticNorm_nonneg V (oddSquarefreeUpTo (N / p.2))
  have hEA := mellinWeightedEnergy_nonneg S a β σ
  have hEB := mellinWeightedEnergy_nonneg T b γ σ
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hrow' (r : ℝ) : (∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V,
      ‖coprimeProductDivisorJacobiRow S T
        (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖) ≤ Real.sqrt E := by
    have h := hrow r
    change _ ≤ E at h
    have hn : 0 ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V,
        ‖coprimeProductDivisorJacobiRow S T
          (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖ :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg E]
  have hweight (r : ℝ) : (∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V, (α d v) ^ (-σ) *
      ‖coprimeProductDivisorJacobiRow S T
        (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖) ≤ H * Real.sqrt E := by
    calc
      _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V,
          H * ‖coprimeProductDivisorJacobiRow S T
            (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖ :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun v hv =>
          mul_le_mul_of_nonneg_right (hαH d hd v hv) (norm_nonneg _)))
      _ = H * ∑ d ∈ Finset.Ioc D (2 * D), ∑ v ∈ V,
          ‖coprimeProductDivisorJacobiRow S T
            (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖ := by
        simp_rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow' r) hH
  apply (coprime_jacobi_range_mellin_separation (Finset.Ioc D (2 * D)) V S T a b
    ρ σ hσ α β γ hα hβ hγ).trans
  have hm := (Ostmann.schwartz_mellin_vertical_integrable ρ σ hσ).norm
  have hi := integral_mono
    (coprime_jacobi_range_mellin_integrable (Finset.Ioc D (2 * D)) V S T a b
      ρ σ hσ α β γ hα hβ hγ)
    (hm.mul_const (H * Real.sqrt E))
    (fun r => mul_le_mul_of_nonneg_left (hweight r) (norm_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ (1 / (2 * Real.pi) : ℝ) by positivity)
  rw [integral_mul_const] at hh
  convert hh using 1
  dsimp only [E]
  ring

end Ostmann.QuadraticSieve

end OAI
