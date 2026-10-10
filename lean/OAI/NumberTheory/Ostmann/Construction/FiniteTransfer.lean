import OAI.NumberTheory.Ostmann.Construction.FiniteStatistic

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

namespace FinitePrior
variable {ι : Type*} [Fintype ι]

def cmean (μ : FinitePrior ι) (f : ι → ℂ) : ℂ := ∑ i, (μ.mass i : ℂ) * f i

theorem norm_cmean_le (μ : FinitePrior ι) (f : ι → ℂ) :
    ‖μ.cmean f‖ ≤ μ.mean (fun i => ‖f i‖) := by
  calc
    ‖μ.cmean f‖ ≤ ∑ i, ‖(μ.mass i : ℂ) * f i‖ := norm_sum_le _ _
    _ = μ.mean (fun i => ‖f i‖) := by
      simp only [mean, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (μ.mass_nonneg _)]

theorem norm_cmean_sq_le (μ : FinitePrior ι) (f : ι → ℂ) :
    ‖μ.cmean f‖^2 ≤ μ.mean (fun i => ‖f i‖^2) := by
  calc
    ‖μ.cmean f‖^2 ≤ (μ.mean (fun i => ‖f i‖))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (μ.norm_cmean_le f) 2
    _ ≤ μ.mean (fun i => ‖f i‖^2) := μ.mean_sq_le _

theorem mean_mono (μ : FinitePrior ι) {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    μ.mean f ≤ μ.mean g := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (μ.mass_nonneg i)

end FinitePrior

theorem row_cauchy {τ : Type*} [Fintype τ] (G B : τ → ℂ) :
    ‖∑ t, G t * B t‖^2 ≤ (∑ t, ‖G t‖^2) * (∑ t, ‖B t‖^2) := by
  have hnorm : ‖∑ t, G t * B t‖ ≤ ∑ t, ‖G t‖ * ‖B t‖ := by
    simpa only [norm_mul] using norm_sum_le (s := Finset.univ) (fun t => G t * B t)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun t => ‖G t‖) (fun t => ‖B t‖))

theorem extracted_row_transfer {ι τ : Type*} [Fintype ι] [Fintype τ]
    (μ : FinitePrior ι) (G B : ι → τ → ℂ) (P : ι → ℝ)
    (hrow : ∀ i, (∑ t, ‖G i t‖^2) ≤ P i) :
    ‖μ.cmean (fun i => ∑ t, G i t * B i t)‖^2 ≤
      μ.mean (fun i => P i * ∑ t, ‖B i t‖^2) := by
  refine (μ.norm_cmean_sq_le _).trans (μ.mean_mono fun i => ?_)
  exact (row_cauchy (G i) (B i)).trans
    (mul_le_mul_of_nonneg_right (hrow i) (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem extend_nonnegative_pivot_sum (primePivots integerPivots : Finset ℕ)
    (primeWeight integerWeight rowSquare : ℕ → ℝ)
    (hsub : primePivots ⊆ integerPivots)
    (hweight : ∀ p ∈ primePivots, primeWeight p = integerWeight p)
    (hnonneg : ∀ p ∈ integerPivots, 0 ≤ integerWeight p * rowSquare p) :
    (∑ p ∈ primePivots, primeWeight p * rowSquare p) ≤
      ∑ p ∈ integerPivots, integerWeight p * rowSquare p := by
  rw [Finset.sum_congr rfl (fun p hp => congrArg (fun w => w * rowSquare p) (hweight p hp))]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnonneg p hp)

end Ostmann.Construction

end

end OAI
