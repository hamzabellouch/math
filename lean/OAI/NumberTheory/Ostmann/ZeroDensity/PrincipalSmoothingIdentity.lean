import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalSmoothingAbel

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace Ostmann.ZeroDensity

theorem principal_integral_Ioi_eq_interval {φ : ℝ → ℝ}
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) :
    (∫ t in Ioi (0 : ℝ), φ t) = ∫ t in (1/2 : ℝ)..1, φ t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (1/2 : ℝ) ≤ 1)]
  have hmem {x : ℝ} (hx : φ x ≠ 0) : x ∈ Ioo (1/2 : ℝ) 1 :=
    hs (subset_tsupport φ (Function.mem_support.mpr hx))
  calc
    _ = ∫ t : ℝ, φ t := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra h
      have h' := (hmem h).1
      exact hx (by change 0 < x; linarith))
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra h
      exact hx ⟨(hmem h).1, (hmem h).2.le⟩)).symm

theorem principal_smoothing_main_term {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1)
    {X : ℝ} (hX : 0 < X) :
    -(∫ t in X/2..X, (deriv φ (t/X) / X) * t) =
      X * ∫ t in Ioi (0 : ℝ), φ t := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := X/2) (b := X)
    (fun t _ => principal_weight_hasDerivAt hφ X t)
    (fun t _ => hasDerivAt_id t)
    ((principal_weight_deriv_continuous hφ X).intervalIntegrable _ _)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (X/2) X)
  have he := principal_weight_endpoints hs hX
  simp only [id_eq, mul_one, he.1, he.2, zero_mul, sub_self, zero_sub] at h
  rw [← h, intervalIntegral.integral_comp_div _ hX.ne']
  have hhalf : X/2/X = (1/2 : ℝ) := by field_simp
  rw [hhalf, div_self hX.ne', smul_eq_mul, ← principal_integral_Ioi_eq_interval hs]

theorem principal_cumulative_deriv_integrable (c : ℕ → ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {X : ℝ} (hX : 0 < X) :
    IntervalIntegrable (fun t => (deriv φ (t/X)/X) * principalCumulative c t)
      volume (X/2) X := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : X/2 ≤ X)).mpr
  exact integrableOn_mul_sum_Icc c (by positivity : 0 ≤ X/2)
    (principal_weight_deriv_continuous hφ X).continuousOn.integrableOn_Icc

theorem principal_smoothing_error_identity (c : ℕ → ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1)
    {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, c n * φ ((n : ℝ)/X)) - X * (∫ t in Ioi (0 : ℝ), φ t) =
      -(∫ t in X/2..X, (deriv φ (t/X)/X) * (principalCumulative c t-t)) := by
  rw [principal_smoothing_abel c hφ hs hX, ← principal_smoothing_main_term hφ hs hX]
  simp_rw [mul_sub]
  have hcont : Continuous (fun t : ℝ => (deriv φ (t/X)/X)*t) := by
    apply Continuous.mul
    · exact principal_weight_deriv_continuous hφ X
    · exact continuous_id
  have ht : IntervalIntegrable (fun t : ℝ => (deriv φ (t/X)/X)*t) volume (X/2) X :=
    hcont.intervalIntegrable (X/2) X
  rw [intervalIntegral.integral_sub (principal_cumulative_deriv_integrable c hφ hX) ht]
  ring

end Ostmann.ZeroDensity

end

end OAI
