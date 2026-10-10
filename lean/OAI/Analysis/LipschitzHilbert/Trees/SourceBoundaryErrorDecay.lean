import OAI.Analysis.LipschitzHilbert.Trees.ResidualBudget

namespace OAI

/-! The actual dyadic boundary radius beats every fixed polynomial.
This pays for the integrated packet error after its entropy bound. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_boundary_error_power_budget (C r Q : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      C*L^r*(4*SourceParameters.step L^(-(1/4:ℝ))) ≤ L^(-Q) := by
  have hlim : Tendsto (fun L => (4*C)*(L^(r+Q)*SourceParameters.step L^(-(1/4:ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (source_polynomial_step_decay (r+Q) (1/4) (by norm_num)).const_mul (4*C)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with L hL hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpower : L^(r+Q)*L^(-Q) = L^r := by
    rw [←Real.rpow_add hL0]
    congr 1
    ring
  calc
    C*L^r*(4*SourceParameters.step L^(-(1/4:ℝ))) =
        ((4*C)*(L^(r+Q)*SourceParameters.step L^(-(1/4:ℝ))))*L^(-Q) := by
      rw [show (4*C)*(L^(r+Q)*SourceParameters.step L^(-(1/4:ℝ)))*L^(-Q) =
        C*(L^(r+Q)*L^(-Q))*(4*SourceParameters.step L^(-(1/4:ℝ))) by ring,hpower]
    _ ≤ 1*L^(-Q) := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hL0.le _)
    _ = L^(-Q) := one_mul _

theorem eventually_boundary_radius_small :
    ∀ᶠ L : ℝ in atTop, 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2 := by
  have hlim : Tendsto (fun L => (4:ℝ)*(L^(0:ℝ)*SourceParameters.step L^(-(1/4:ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (source_polynomial_step_decay 0 (1/4) (by norm_num)).const_mul 4
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with L hL
  simpa only [Real.rpow_zero,one_mul] using hL.le

end LipschitzHilbert

end

end OAI
