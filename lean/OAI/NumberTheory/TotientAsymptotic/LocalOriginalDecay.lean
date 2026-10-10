import OAI.NumberTheory.TotientAsymptotic.LocalOriginalPruning
import OAI.NumberTheory.TotientAsymptotic.FixedPrefixLower
import OAI.NumberTheory.TotientAsymptotic.FordDimensionScale

namespace OAI

/-! Original-head errors vanish on the same fixed-prefix normalization
as the positive candidate family. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem ambient_residual_error_negligible (H : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      x/Real.log x*(rho^(m x)+2*(B x)^(-4:ℝ)) ≤
        ε*(x/Real.log x*G x (m x-H)) := by
  obtain ⟨c,hc,hprefix⟩ := fixed_prefix_volume_lower H
  have hr : Tendsto (fun x : ℝ => rho^(m x)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).comp m_tendsto
  have hp : Tendsto (fun x : ℝ => (B x)^(-4:ℝ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<4)).comp B_tendsto
  have he : Tendsto (fun x : ℝ => rho^(m x)+2*(B x)^(-4:ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,zero_add] using hr.add (hp.const_mul 2)
  filter_upwards [he.eventually (eventually_lt_nhds (mul_pos hε hc)),
    hprefix,central_volume_one_le,eventually_gt_atTop (1:ℝ)] with x hx hpref hG hx1
  have hcG : c ≤ G x (m x-H) :=
    (le_mul_of_one_le_right hc.le hG).trans hpref
  have hcoeff : rho^(m x)+2*(B x)^(-4:ℝ) ≤ ε*G x (m x-H) :=
    hx.le.trans (mul_le_mul_of_nonneg_left hcG hε.le)
  have hscale : 0 ≤ x/Real.log x :=
    div_nonneg (zero_lt_one.trans hx1).le (Real.log_pos hx1).le
  calc
    _ ≤ (x/Real.log x)*(ε*G x (m x-H)) := mul_le_mul_of_nonneg_left hcoeff hscale
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
