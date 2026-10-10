import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszPerronExpansion
import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerronAll

namespace OAI

/-! # The all-order expansion of the actual squarefree Riesz sum -/
namespace JointDickman
open Complex Filter Asymptotics Finset
open scoped Topology

theorem squarefreeRieszSum_normalized_perron {z L : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hL : 0 < L) :
    (squarefreeRieszSum z (Real.exp L)).re / Real.exp L =
      (VerticalIntegral' (squarefreeNormalizedPerron z L) (1/L)).re := by
  have h := congrArg Complex.re (squarefreeNormalizedPerron_riesz_all (L := L) hz hz1 (one_div_pos.mpr hL))
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] at h
  exact (div_eq_iff (Real.exp_pos L).ne').mpr (by nlinarith)

theorem squarefreeRieszSum_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z/2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun x : ℝ => (squarefreeRieszSum z x).re -
        x*∑ j ∈ range (H+1), c j*(Real.log x)^(z-1-j)) =O[atTop]
        (fun x => x*(Real.log x)^(z-2-H)) := by
  obtain ⟨c,hc,hc0,hperron⟩ := squarefreeRiesz_perron_expansion hz hz1
  refine ⟨c,hc,hc0,fun H => ?_⟩
  have h := (isBigO_refl (fun L : ℝ => Real.exp L) atTop).mul (hperron H)
  have hexp : (fun L : ℝ => (squarefreeRieszSum z (Real.exp L)).re -
      Real.exp L*∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop]
      (fun L => Real.exp L*L^(z-2-H)) := by
    apply h.congr'
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
      have he := squarefreeRieszSum_normalized_perron hz.le hz1.le hL
      change Real.exp L*((VerticalIntegral' (squarefreeNormalizedPerron z L) (1/L)).re -
        ∑ j ∈ range (H+1), c j*L^(z-1-j)) = _
      rw [←he]
      field_simp
    · rfl
  have hlog := hexp.comp_tendsto Real.tendsto_log_atTop
  apply hlog.congr'
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [Function.comp_apply,Real.exp_log hx]
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [Function.comp_apply,Real.exp_log hx]

end JointDickman

end OAI
