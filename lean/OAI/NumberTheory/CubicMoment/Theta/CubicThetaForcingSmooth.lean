import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingSeries

namespace OAI

/-! Smoothness of the actual forcing follows from the compact cutoff
and the locally finite arithmetic row expansion. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaIncomingForcing_contDiffAt (s : ℂ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ ∞ (cubicThetaIncomingForcing s) v := by
  have hd := (contDiff_infty_iff_deriv.mp cubicThetaCuspCutoff_smooth).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => (t:ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt
  have hp := (cubicThetaHeightPower_analytic s hv).contDiffAt (n:=∞)
  have hp' := (cubicThetaHeightPower_analytic (s-1) hv).contDiffAt (n:=∞)
  exact (((hc.pow 2).mul hdd.contDiffAt).sub (hc.mul hd.contDiffAt)).mul hp |>.add
    (((((contDiffAt_const.mul (hc.pow 2)).mul hd.contDiffAt).mul
      contDiffAt_const).mul hp'))

lemma cubicThetaForcingTerm_contDiffAt (r : CubicThetaBottomRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaForcingTerm r q s) p :=
  contDiffAt_const.mul ((cubicThetaIncomingForcing_contDiffAt s (r.height_pos hp)).comp p
    (r.height_contDiffAt hp))

theorem cubicThetaForcingSeries_contDiffOn (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaForcingSeries p s)
      {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaForcingSeries_compact_sum hK hKpos
  have he : (fun q => cubicThetaForcingSeries q s) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaForcingTerm r q s) := by
    filter_upwards [hKn] with q hq
    exact (hS q hq s).2
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaForcingTerm r q s) p :=
    ContDiffAt.sum (fun r _ => cubicThetaForcingTerm_contDiffAt r s hp)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

end CubicFirstMoment

end

end OAI
