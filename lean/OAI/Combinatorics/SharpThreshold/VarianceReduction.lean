import OAI.Combinatorics.SharpThreshold.SpectralBounds
import OAI.Combinatorics.SharpThreshold.ExpQuadratic

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- The graph-independent final step of the variance proof: capture at squared
logarithmic degree, together with Parseval and the Dirichlet identity, yields
the exact advertised numerical constant. -/
theorem variance_bound_of_fourier_capture {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma influence t m : ℝ)
    (hsigma : 0 < sigma) (hinfluence : 0 ≤ influence)
    (ht : 0 < t) (hm : 0 < m) (hlog : t / 3 ≤ Real.log m)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * Real.log m / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ (4 * m ^ (-1 / 4 : ℝ)) * influence) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence := by
  have hell : 0 < Real.log m := lt_of_lt_of_le (by positivity : 0 < t / 3) hlog
  have hpre := variance_from_fourier_capture coeff variance sigma (Real.log m)
    influence (4 * m ^ (-1 / 4 : ℝ)) hsigma hell hvariance hdirichlet hcapture
  have hrem : 4 * m ^ (-1 / 4 : ℝ) ≤ 2304 / t ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).2
    exact block_rpow_remainder_le t m ht.le hm hlog
  have hconstant := variance_constant_assembly_budget t (Real.log m)
    (4 * m ^ (-1 / 4 : ℝ)) 2304 ht hlog hrem (by norm_num)
  exact hpre.trans (mul_le_mul_of_nonneg_right hconstant hinfluence)

/-- A complete numerical reduction for all logarithmic scales. The only
large-scale input remaining is capture of low Fourier supports. -/
theorem variance_bound_of_fourier_inputs {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma influence t : ℝ)
    (hsigma : 0 < sigma) (hsigma_sq : sigma ^ 2 ≤ 1 / 4)
    (hinfluence : 0 ≤ influence) (ht : 0 < t)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : 16 ≤ t → ∃ m : ℝ, 0 < m ∧ t / 3 ≤ Real.log m ∧
      (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * Real.log m / 64) ^ 2 / 2, coeff S ^ 2)
        ≤ (4 * m ^ (-1 / 4 : ℝ)) * influence) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence := by
  by_cases hlarge : 16 ≤ t
  · obtain ⟨m, hm, hlog, hcap⟩ := hcapture hlarge
    exact variance_bound_of_fourier_capture coeff variance sigma influence t m
      hsigma hinfluence ht hm hlog hvariance hdirichlet hcap
  · have hpoincare := variance_le_dirichlet_of_fourier coeff variance
      (sigma ^ 2 * influence) hvariance hdirichlet
    have hquarter : variance ≤ influence / 4 := by
      have h := mul_le_mul_of_nonneg_right hsigma_sq hinfluence
      linarith
    exact variance_small_log_assembly t variance influence ht (by linarith)
      hinfluence hquarter

end Problem313

end

end OAI
