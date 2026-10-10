import OAI.NumberTheory.Ostmann.QuadraticSieveMellinSeparationBasic

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

noncomputable def bilinearMellinRow {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (K : ι → κ → ℂ) (β : ι → ℝ) (γ : κ → ℝ) (σ r : ℝ) : ℂ :=
  ∑ n ∈ S, ∑ t ∈ T, K n t * mellinScale σ r (β n) * mellinScale σ r (γ t)

theorem bilinear_mellin_integrand_eq {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (K : ι → κ → ℂ) (α : ℝ) (β : ι → ℝ) (γ : κ → ℝ) (σ r : ℝ) (M : ℂ)
    (hα : 0 < α) (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    (∑ n ∈ S, ∑ t ∈ T, K n t * (mellinScale σ r (α * β n * γ t) * M)) =
      mellinScale σ r α * M * bilinearMellinRow S T K β γ σ r := by
  unfold bilinearMellinRow
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  rw [mellinScale_mul σ r (α * β n) (γ t) (mul_pos hα (hβ n hn)) (hγ t ht),
    mellinScale_mul σ r α (β n) hα (hβ n hn)]
  ring

theorem bilinear_mellin_integrand_integrable {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    (K : ι → κ → ℂ) (α : ℝ) (β : ι → ℝ) (γ : κ → ℝ)
    (hα : 0 < α) (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    Integrable (fun r : ℝ => mellinScale σ r α * mellin (ρ : ℝ → ℂ) (σ + r * Complex.I) *
      bilinearMellinRow S T K β γ σ r) := by
  have hf : Integrable (fun r : ℝ => ∑ n ∈ S, ∑ t ∈ T, K n t *
      (mellinScale σ r (α * β n * γ t) * mellin (ρ : ℝ → ℂ) (σ + r * Complex.I))) := by
    apply integrable_finsetSum
    intro n hn
    apply integrable_finsetSum
    intro t ht
    exact (mellinScale_mul_mellin_integrable ρ σ hσ (α * β n * γ t)
      (mul_pos (mul_pos hα (hβ n hn)) (hγ t ht))).const_mul (K n t)
  exact hf.congr (ae_of_all _ (fun r =>
    bilinear_mellin_integrand_eq S T K α β γ σ r _ hα hβ hγ))

theorem bilinear_mellin_inversion {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    (K : ι → κ → ℂ) (α : ℝ) (β : ι → ℝ) (γ : κ → ℝ)
    (hα : 0 < α) (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    (∑ n ∈ S, ∑ t ∈ T, K n t * ρ (α * β n * γ t)) =
      (1 / (2 * Real.pi) : ℝ) •
        (∫ r : ℝ, mellinScale σ r α * mellin (ρ : ℝ → ℂ) (σ + r * Complex.I) *
          bilinearMellinRow S T K β γ σ r) := by
  classical
  have hx (p : ι × κ) (hp : p ∈ S ×ˢ T) : 0 < α * β p.1 * γ p.2 :=
    mul_pos (mul_pos hα (hβ p.1 (Finset.mem_product.mp hp).1))
      (hγ p.2 (Finset.mem_product.mp hp).2)
  have h := finite_mellin_inversion (S ×ˢ T) ρ σ hσ
    (fun p => K p.1 p.2) (fun p => α * β p.1 * γ p.2) hx
  simp only [Finset.sum_product] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun r => bilinear_mellin_integrand_eq S T K α β γ σ r _ hα hβ hγ)

end Ostmann.QuadraticSieve

end OAI
