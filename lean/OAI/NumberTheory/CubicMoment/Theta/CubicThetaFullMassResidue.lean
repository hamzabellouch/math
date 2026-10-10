import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRegularHeatPole
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

namespace OAI

/-! The exact residue of the full affine-row norm series. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaRealGamma_continuousAt_two : ContinuousAt Real.Gamma 2 := by
  have h : ContinuousAt Complex.Gamma (2:ℂ) := Complex.continuousAt_Gamma 2 (by
    intro n hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
    linarith)
  have hc : ContinuousAt (fun s : ℝ => Complex.Gamma (s:ℂ)) 2 :=
    h.comp (f:=fun s : ℝ => (s:ℂ)) Complex.continuous_ofReal.continuousAt
  exact Complex.continuous_re.continuousAt.comp
    (f:=fun s : ℝ => Complex.Gamma (s:ℂ)) hc

lemma cubicThetaRealGamma_two : Real.Gamma 2=1 := by
  norm_num

theorem cubicThetaFullHeightMass_residue {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun s : ℝ => (s-2)*cubicThetaFullHeightMass p s) (𝓝[>] 2)
      (𝓝 (4*Real.pi^2/243)) := by
  let C := 4*Real.pi^2/243
  have hzero : Tendsto (fun s : ℝ => s-2) (𝓝[>] 2) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℝ => s-2) 2 := by fun_prop
    simpa only [sub_self] using h.tendsto.mono_left
      (show 𝓝[>] (2:ℝ)≤𝓝 2 from nhdsWithin_le_nhds)
  have hR := cubicThetaRegularHeatMass_tendsto hp
  have hnum : Tendsto (fun s : ℝ => C+(s-2)*cubicThetaRegularHeatMass p s)
      (𝓝[>] 2) (𝓝 C) := by
    simpa using tendsto_const_nhds.add (hzero.mul hR)
  have hG : Tendsto Real.Gamma (𝓝[>] (2:ℝ)) (𝓝 1) := by
    simpa only [cubicThetaRealGamma_two] using
      cubicThetaRealGamma_continuousAt_two.tendsto.mono_left nhdsWithin_le_nhds
  have hd := hnum.div hG (by norm_num : (1:ℝ)≠0)
  simp only [div_one] at hd
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 2<s at hs
  have he := cubicThetaFullHeightMass_pole_identity hp hs
  have hGamma := (Real.Gamma_pos_of_pos (lt_trans (by norm_num) hs)).ne'
  apply (div_eq_iff hGamma).mpr
  have hne : s-2≠0 := by linarith
  dsimp [C]
  field_simp [hne] at he
  nlinarith [he]

end CubicFirstMoment

end

end OAI
