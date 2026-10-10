import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor

namespace OAI

/-! Uniform coordinate scale at each fixed distance below the natural dimension. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma direct_scale_eq {x : ℝ} (hB : 1 < B x) (hm : 0 < m x) :
    B x*rho^(m x)/(m x:ℝ)=alpha (theta x)*bandCenterRatio x := by
  have hh := inverse_scale_eq hB hm
  have hi := congrArg (fun z : ℝ => z⁻¹) hh
  simpa only [inv_div,inv_inv] using hi

lemma natural_coordinate_scale_upper : ∃ A : ℝ,0 < A ∧
    ∀ H : ℕ,∀ᶠ x : ℝ in atTop,
      0 < m x-H ∧ B x*rho^(m x)/((m x-H:ℕ):ℝ) ≤ A := by
  refine ⟨4*lam/rho,div_pos (mul_pos (by norm_num) lam_pos) rho_pos,?_⟩
  intro H
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (1:ℝ)),
    m_tendsto.eventually (eventually_gt_atTop (2*H)),
    bandCenterRatio_tendsto.eventually (eventually_lt_nhds (by norm_num : (1:ℝ)<2)),
    bandCenterRatio_tendsto.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))]
    with x hphase hB hm hc hc0
  have hm0 : 0 < m x := by omega
  have hn : 0 < m x-H := by omega
  refine ⟨hn,?_⟩
  have hbasic : B x*rho^(m x)/(m x:ℝ) ≤ 2*lam/rho := by
    rw [direct_scale_eq hB hm0]
    have hh := mul_le_mul (alpha_le _ hphase) hc.le hc0.le
      (div_pos lam_pos rho_pos).le
    exact hh.trans_eq (by ring)
  have hsize : (m x:ℝ) ≤ 2*((m x-H:ℕ):ℝ) := by
    exact_mod_cast (show m x ≤ 2*(m x-H) by omega)
  have hnm : (0:ℝ) < ((m x-H:ℕ):ℝ) := by exact_mod_cast hn
  have hbasic' := (div_le_iff₀ (show (0:ℝ) < (m x:ℝ) by exact_mod_cast hm0)).mp hbasic
  apply (div_le_iff₀ hnm).mpr
  have hmul := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 2*lam/rho from (div_pos (mul_pos (by norm_num) lam_pos) rho_pos).le)
  exact hbasic'.trans (hmul.trans_eq (by ring))

end TotientAsymptotic

end

end OAI
