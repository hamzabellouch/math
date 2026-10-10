import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMollifierProduct
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDiscreteHybrid

namespace OAI

/-! # Vertical Dirichlet polynomials with the actual complex powers -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def densityVerticalPoint (σ t : ℝ) : ℂ :=
  (σ : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * t

noncomputable def densityVerticalCoeff (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ :=
  a n / (n : ℂ) ^ (σ : ℂ)

 theorem density_vertical_term (a : ℂ) (σ t : ℝ) (n : ℕ) (hn : 0 < n) :
    a / (n : ℂ) ^ densityVerticalPoint σ t =
      (a / (n : ℂ) ^ (σ : ℂ)) * realAdditivePhase (-(Real.log n * t)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (show (0 : ℝ) ≤ n by positivity)).symm
  have he : ((n : ℂ) ^ (2 * (Real.pi : ℂ) * Complex.I * t))⁻¹ =
      realAdditivePhase (-(Real.log n * t)) := by
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_neg, hlog]
    unfold realAdditivePhase
    congr 1
    push_cast
    ring
  rw [densityVerticalPoint, Complex.cpow_add _ _ hnC, div_mul_eq_div_mul_one_div,
    one_div, he]

 theorem density_vertical_polynomial (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    (a : ℕ → ℂ) (σ t : ℝ) :
    (∑ n ∈ S, a n / (n : ℂ) ^ densityVerticalPoint σ t) =
      ∑ n ∈ S, densityVerticalCoeff a σ n * realAdditivePhase (-(Real.log n * t)) := by
  exact Finset.sum_congr rfl (fun n hn => density_vertical_term _ σ t n (hS n hn))

 theorem densityVerticalCoeff_norm (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖densityVerticalCoeff a σ n‖ = ‖a n‖ / (n : ℝ) ^ σ := by
  rw [densityVerticalCoeff, norm_div]
  congr 1
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  rfl

 theorem densityVerticalCoeff_half_square (a : ℕ → ℂ) (n : ℕ) (hn : 0 < n) :
    ‖densityVerticalCoeff a (1 / 2) n‖ ^ 2 = ‖a n‖ ^ 2 / n := by
  have hden : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [densityVerticalCoeff_norm a _ n hn, div_pow, hden]

end Ostmann

end OAI
