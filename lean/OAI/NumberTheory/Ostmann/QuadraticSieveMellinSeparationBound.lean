import OAI.NumberTheory.Ostmann.QuadraticSieveMellinSeparationRows

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

theorem bilinear_mellin_norm_weight_integrable {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    (K : ι → κ → ℂ) (α : ℝ) (β : ι → ℝ) (γ : κ → ℝ)
    (hα : 0 < α) (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    Integrable (fun r : ℝ => ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖ *
      (α ^ (-σ) * ‖bilinearMellinRow S T K β γ σ r‖)) := by
  apply (bilinear_mellin_integrand_integrable S T ρ σ hσ K α β γ hα hβ hγ).norm.congr
  apply ae_of_all
  intro r
  dsimp only
  rw [norm_mul, norm_mul, norm_mellinScale σ r α hα]
  ring

theorem bilinear_mellin_norm_le {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    (K : ι → κ → ℂ) (α : ℝ) (β : ι → ℝ) (γ : κ → ℝ)
    (hα : 0 < α) (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    ‖∑ n ∈ S, ∑ t ∈ T, K n t * ρ (α * β n * γ t)‖ ≤
      (1 / (2 * Real.pi)) * (∫ r : ℝ,
        ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖ *
          (α ^ (-σ) * ‖bilinearMellinRow S T K β γ σ r‖)) := by
  rw [bilinear_mellin_inversion S T ρ σ hσ K α β γ hα hβ hγ,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 / (2 * Real.pi) : ℝ))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  apply ae_of_all
  intro r
  dsimp only
  rw [norm_mul, norm_mul, norm_mellinScale σ r α hα]
  ring

theorem finite_bilinear_mellin_weight_integrable {υ ι κ : Type*}
    (V : Finset υ) (S : Finset ι) (T : Finset κ)
    (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    (K : υ → ι → κ → ℂ) (α : υ → ℝ) (β : ι → ℝ) (γ : κ → ℝ)
    (hα : ∀ v ∈ V, 0 < α v) (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    Integrable (fun r : ℝ => ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖ *
      ∑ v ∈ V, (α v) ^ (-σ) * ‖bilinearMellinRow S T (K v) β γ σ r‖) := by
  simp only [Finset.mul_sum]
  exact integrable_finsetSum V (fun v hv =>
    bilinear_mellin_norm_weight_integrable S T ρ σ hσ (K v) (α v) β γ (hα v hv) hβ hγ)

theorem finite_bilinear_mellin_separation {υ ι κ : Type*}
    (V : Finset υ) (S : Finset ι) (T : Finset κ)
    (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    (K : υ → ι → κ → ℂ) (α : υ → ℝ) (β : ι → ℝ) (γ : κ → ℝ)
    (hα : ∀ v ∈ V, 0 < α v) (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    (∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T, K v n t * ρ (α v * β n * γ t)‖) ≤
      (1 / (2 * Real.pi)) * (∫ r : ℝ,
        ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖ *
          ∑ v ∈ V, (α v) ^ (-σ) * ‖bilinearMellinRow S T (K v) β γ σ r‖) := by
  calc
    _ ≤ ∑ v ∈ V, (1 / (2 * Real.pi)) * (∫ r : ℝ,
        ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖ *
          ((α v) ^ (-σ) * ‖bilinearMellinRow S T (K v) β γ σ r‖)) :=
      Finset.sum_le_sum (fun v hv =>
        bilinear_mellin_norm_le S T ρ σ hσ (K v) (α v) β γ (hα v hv) hβ hγ)
    _ = _ := by
      rw [← Finset.mul_sum, ← integral_finsetSum V (fun v hv =>
        bilinear_mellin_norm_weight_integrable S T ρ σ hσ (K v) (α v) β γ (hα v hv) hβ hγ)]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun r => (Finset.mul_sum V _ _).symm)

end Ostmann.QuadraticSieve

end OAI
