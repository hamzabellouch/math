import OAI.Analysis.CircleDomains.Sobolev.PrincipalCircleAreaEstimate

namespace OAI

/-! The principal exterior germ determines the limiting signed image area. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_circle_area_limit {F : ℂ → ℂ} {c : ℂ} {T : ℂ → ℂ}
    (hT : AnalyticAt ℂ T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = c*z⁻¹+z⁻¹^2*T z⁻¹) :
    Tendsto (fun R : ℝ => signedCurveArea (fun t => F (unitCircleParam 0 R t)) -
      Real.pi*R^2) atTop (𝓝 0) := by
  obtain ⟨B, C, hB, hC, hbounds⟩ := analytic_inverse_circle_bounds hT
  let M := principalAreaErrorBudget (1+‖c‖) B C
  have hlim : Tendsto (fun R : ℝ => M/R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)))
  have herr : Tendsto (fun R : ℝ => signedCurveArea (fun t => F (unitCircleParam 0 R t)) -
      signedCurveArea (principalLeadingCurve R c)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hbounds] with R hR
    rw [Real.norm_eq_abs, principal_leading_circle_area R
      (lt_of_lt_of_le zero_lt_one hR.1) c]
    exact principal_circle_area_estimate hexp hR.1 hB hC
      (fun t => (hR.2 t).1) (fun t => (hR.2 t).2.1) (fun t => (hR.2 t).2.2)
  have hbase : Tendsto (fun R : ℝ => signedCurveArea (principalLeadingCurve R c) -
      Real.pi*R^2) atTop (𝓝 0) := by
    have hh : Tendsto (fun R : ℝ => (-Real.pi*‖c‖^2)*(R⁻¹)^2) atTop (𝓝 0) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
        ((tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).pow 2).const_mul
          (-Real.pi*‖c‖^2)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [principal_leading_circle_area R hR c]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have hh := herr.add hbase
  convert hh using 1
  · funext R
    ring
  · simp

end CircleDomainRigidity

end

end OAI
