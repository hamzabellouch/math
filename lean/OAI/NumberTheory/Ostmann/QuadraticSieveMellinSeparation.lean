import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationProduct
import OAI.NumberTheory.Ostmann.QuadraticSieveMellinSeparationBound

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

noncomputable def mellinTwist (σ r : ℝ) (β : ℕ → ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * mellinScale σ r (β n)

noncomputable def coprimeMellinJacobiKernel (a b : ℕ → ℂ) (d v n t : ℕ) : ℂ :=
  if n.Coprime t ∧ d ∣ n * t then a n * b t * (jacobiSym (v : ℤ) (n * t) : ℂ) else 0

theorem bilinearMellinRow_jacobi (S T : Finset ℕ) (a b : ℕ → ℂ) (d v : ℕ)
    (β γ : ℕ → ℝ) (σ r : ℝ) :
    bilinearMellinRow S T (coprimeMellinJacobiKernel a b d v) β γ σ r =
      coprimeProductDivisorJacobiRow S T (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ) := by
  unfold bilinearMellinRow coprimeProductDivisorJacobiRow
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  simp only [coprimeMellinJacobiKernel, mellinTwist]
  split_ifs <;> ring

theorem coprime_jacobi_mellin_separation (V S T : Finset ℕ) (a b : ℕ → ℂ) (d : ℕ)
    (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) (α β γ : ℕ → ℝ)
    (hα : ∀ v ∈ V, 0 < α v) (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    (∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
      if n.Coprime t ∧ d ∣ n * t then
        a n * b t * (jacobiSym (v : ℤ) (n * t) : ℂ) * ρ (α v * β n * γ t) else 0‖) ≤
      (1 / (2 * Real.pi)) * (∫ r : ℝ,
        ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖ *
          ∑ v ∈ V, (α v) ^ (-σ) *
            ‖coprimeProductDivisorJacobiRow S T
              (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖) := by
  have h := finite_bilinear_mellin_separation V S T ρ σ hσ
    (coprimeMellinJacobiKernel a b d) α β γ hα hβ hγ
  simp_rw [bilinearMellinRow_jacobi] at h
  simpa only [coprimeMellinJacobiKernel, ite_mul, zero_mul] using h

theorem coprime_jacobi_mellin_weight_integrable (V S T : Finset ℕ) (a b : ℕ → ℂ) (d : ℕ)
    (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) (α β γ : ℕ → ℝ)
    (hα : ∀ v ∈ V, 0 < α v) (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    Integrable (fun r : ℝ => ‖mellin (ρ : ℝ → ℂ) (σ + r * Complex.I)‖ *
      ∑ v ∈ V, (α v) ^ (-σ) *
        ‖coprimeProductDivisorJacobiRow S T
          (mellinTwist σ r β a) (mellinTwist σ r γ b) d (v : ℤ)‖) := by
  simpa only [bilinearMellinRow_jacobi] using
    finite_bilinear_mellin_weight_integrable V S T ρ σ hσ
      (coprimeMellinJacobiKernel a b d) α β γ hα hβ hγ

theorem coefficientEnergy_mellinTwist (S : Finset ℕ) (a : ℕ → ℂ) (β : ℕ → ℝ)
    (σ r : ℝ) (hβ : ∀ n ∈ S, 0 < β n) :
    coefficientEnergy S (mellinTwist σ r β a) =
      ∑ n ∈ S, ‖a n‖ ^ 2 * ((β n) ^ (-σ)) ^ 2 := by
  unfold coefficientEnergy
  apply Finset.sum_congr rfl
  intro n hn
  rw [mellinTwist, norm_mul, norm_mellinScale σ r (β n) (hβ n hn), mul_pow]

end Ostmann.QuadraticSieve

end OAI
