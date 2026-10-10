import OAI.NumberTheory.Ostmann.QuadraticSieveMellinBoundary

namespace OAI

namespace Ostmann
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap

theorem schwartz_mellin_deriv (ρ : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    mellin (SchwartzMap.derivCLM ℂ ℂ ρ : ℝ → ℂ) (s + 1) =
      -s * mellin (ρ : ℝ → ℂ) s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hD : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * deriv ρ x) (Ioi 0) := by
    simpa only [MellinConvergent, add_sub_cancel_right, smul_eq_mul,
      SchwartzMap.derivCLM_apply] using
      schwartz_mellin_convergent (SchwartzMap.derivCLM ℂ ℂ ρ)
        (s := s + 1) (by simpa using (show 0 < s.re + 1 by linarith))
  have hU : IntegrableOn (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * ρ x) (Ioi 0) := by
    simpa only [MellinConvergent, IntegrableOn, smul_eq_mul, mul_assoc] using
      (schwartz_mellin_convergent ρ hs).const_mul s
  have hi := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => (x : ℂ) ^ s) (v := fun x : ℝ => ρ x)
    (u' := fun x : ℝ => s * (x : ℂ) ^ (s - 1)) (v' := fun x : ℝ => deriv ρ x)
    (a := 0) (a' := (0 : ℂ)) (b' := (0 : ℂ))
    (fun x hx => hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hs0)
    (fun x _ => ρ.hasDerivAt x) hD hU
    (schwartz_cpow_mul_tendsto_zero ρ hs) (schwartz_cpow_mul_tendsto_atTop ρ s)
  simp only [mul_assoc, integral_const_mul, sub_self, zero_sub] at hi
  simpa only [mellin, add_sub_cancel_right, smul_eq_mul, SchwartzMap.derivCLM_apply,
    neg_mul] using hi

noncomputable def mellinVerticalBound (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ (σ - 1) * ‖ρ x‖

theorem mellinVerticalBound_nonneg (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) :
    0 ≤ mellinVerticalBound ρ σ := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (norm_nonneg _)

theorem norm_mellin_le_verticalBound (ρ : 𝓢(ℝ, ℂ)) (s : ℂ) :
    ‖mellin (ρ : ℝ → ℂ) s‖ ≤ mellinVerticalBound ρ s.re := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re,
    Complex.one_re]

end Ostmann

end OAI
