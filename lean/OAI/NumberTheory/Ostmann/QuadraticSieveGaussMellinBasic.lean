import OAI.NumberTheory.Ostmann.QuadraticSieveGaussDivisorRanges
import OAI.NumberTheory.Ostmann.QuadraticSieveMellinDivisorRanges

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

noncomputable def gaussMellinKernel (a b : ℕ → ℂ) (c : ℤ) (d v n t : ℕ) : ℂ :=
  if Nat.Coprime n t ∧ d ∣ n*t then
    a n*b t*(jacobiGaussRatio (n*t)*(jacobiSym (c*(v : ℤ)) (n*t) : ℂ)) else 0

theorem bilinearMellinRow_gauss (S T : Finset ℕ) (a b : ℕ → ℂ)
    (c : ℤ) (d v : ℕ) (β γ : ℕ → ℝ) (σ r : ℝ) :
    bilinearMellinRow S T (gaussMellinKernel a b c d v) β γ σ r =
      gaussProductDivisorJacobiRow S T (mellinTwist σ r β a) (mellinTwist σ r γ b) c d (v : ℤ) := by
  unfold bilinearMellinRow gaussMellinKernel gaussProductDivisorJacobiRow
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : Nat.Coprime n t ∧ d ∣ n*t
  · simp only [ite_eq_left h,mellinTwist]
    ring
  · simp only [ite_eq_right h,zero_mul]

theorem gauss_range_mellin_separation (D V S T : Finset ℕ) (a b : ℕ → ℂ)
    (c : ℤ) (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) (α : ℕ → ℕ → ℝ) (β γ : ℕ → ℝ)
    (hα : ∀ d ∈ D, ∀ v ∈ V, 0 < α d v)
    (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    (∑ d ∈ D, ∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
      gaussMellinKernel a b c d v n t * ρ (α d v*β n*γ t)‖) ≤
      (1/(2*Real.pi))*(∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖*
        ∑ d ∈ D, ∑ v ∈ V, (α d v)^(-σ)*
          ‖gaussProductDivisorJacobiRow S T (mellinTwist σ r β a)
            (mellinTwist σ r γ b) c d (v : ℤ)‖) := by
  have h := finite_bilinear_mellin_separation (D ×ˢ V) S T ρ σ hσ
    (fun p => gaussMellinKernel a b c p.1 p.2) (fun p => α p.1 p.2) β γ
    (fun p hp => hα p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) hβ hγ
  simpa only [Finset.sum_product,bilinearMellinRow_gauss] using h

theorem gauss_range_mellin_integrable (D V S T : Finset ℕ) (a b : ℕ → ℂ)
    (c : ℤ) (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) (α : ℕ → ℕ → ℝ) (β γ : ℕ → ℝ)
    (hα : ∀ d ∈ D, ∀ v ∈ V, 0 < α d v)
    (hβ : ∀ n ∈ S, 0 < β n) (hγ : ∀ t ∈ T, 0 < γ t) :
    Integrable (fun r : ℝ => ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖*
      ∑ d ∈ D, ∑ v ∈ V, (α d v)^(-σ)*
        ‖gaussProductDivisorJacobiRow S T (mellinTwist σ r β a)
          (mellinTwist σ r γ b) c d (v : ℤ)‖) := by
  have h := finite_bilinear_mellin_weight_integrable (D ×ˢ V) S T ρ σ hσ
    (fun p => gaussMellinKernel a b c p.1 p.2) (fun p => α p.1 p.2) β γ
    (fun p hp => hα p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) hβ hγ
  simpa only [Finset.sum_product,bilinearMellinRow_gauss] using h

end Ostmann.QuadraticSieve

end OAI
