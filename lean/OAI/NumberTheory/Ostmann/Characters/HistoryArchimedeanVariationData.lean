import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationPolynomial

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Polynomial Set
open scoped BigOperators SchwartzMap

structure HistoryPolynomialData (σ τ : Type*) where
  profile : τ → HistoryProfile
  scale : τ → ℝ
  supports : σ → ℝ[X]
  strict : σ → Bool
  arguments : τ → ℝ[X]
  denominator : τ → ℝ

namespace HistoryPolynomialData
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

def weight (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ)) : ℝ → ℂ :=
  polynomialHistoryWeight ρ d.profile d.scale d.supports d.strict d.arguments d.denominator

def degreeCost (d : HistoryPolynomialData σ τ) : ℕ :=
  2 * ((∑ i, (d.supports i).natDegree) + ∑ i, ((d.arguments i).natDegree - 1)) + 1

structure Ranges (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ))
    (A B : τ → ℝ) (M : ℝ) : Prop where
  nonneg : 0 ≤ M
  ordered : ∀ i, A i ≤ B i
  scale_pos : ∀ i, 0 < d.scale i
  argument_pos : ∀ t, polynomialSupport d.supports d.strict t →
    ∀ i, 0 < (d.arguments i).eval t / d.denominator i
  log_range : ∀ t, polynomialSupport d.supports d.strict t → ∀ i,
    Real.log (d.scale i / ((d.arguments i).eval t / d.denominator i)) ∈ Icc (A i) (B i)
  bound : ∀ i, (d.profile i).bound ρ (B i) ≤ M

def variationCost (d : HistoryPolynomialData σ τ) (A B : τ → ℝ) (M : ℝ) : ℝ :=
  d.degreeCost * (M ^ (Fintype.card τ) * (3 + (∑ i : τ, (B i - A i))))

theorem variationCost_nonneg (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ))
    {A B : τ → ℝ} {M : ℝ} (h : d.Ranges ρ A B M) : 0 ≤ d.variationCost A B M := by
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg h.nonneg _)
    (add_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (h.ordered i)))))

theorem progressionVariation_le (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ))
    {A B : τ → ℝ} {M : ℝ} (h : d.Ranges ρ A B M) (Q a N : ℕ) :
    progressionVariation (fun n => d.weight ρ ((Q*n+a : ℕ) : ℝ)) N ≤
      d.variationCost A B M := by
  exact (progressionVariation_le_pieces (polynomialSupportCuts d.supports d.arguments) Q a _ N).trans
    (polynomialHistoryWeight_total_variation_le ρ d.profile d.scale d.supports d.strict
      d.arguments d.denominator A B Q a N h.nonneg h.ordered h.scale_pos
      h.argument_pos h.log_range h.bound)

theorem scaled_progressionVariation_le (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ))
    {A B : τ → ℝ} {M : ℝ} (h : d.Ranges ρ A B M) (Q a N : ℕ)
    (c : ℂ) (w : ℕ → ℂ)
    (heq : ∀ n : ℕ, n ≤ N → w n = c*d.weight ρ ((Q*n+a : ℕ) : ℝ)) :
    progressionVariation w N ≤ ‖c‖*d.variationCost A B M := by
  rw [progressionVariation_congr N w _ heq, progressionVariation_const_mul]
  exact mul_le_mul_of_nonneg_left (d.progressionVariation_le ρ h Q a N) (norm_nonneg _)

end HistoryPolynomialData
end Ostmann.Characters

end

end OAI
