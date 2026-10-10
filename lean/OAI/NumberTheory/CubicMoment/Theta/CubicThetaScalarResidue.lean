import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullMassResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarResidueReduction

namespace OAI

/-! The actual scalar Eisenstein residue at two, computed from the affine
lattice and the exact primary common-factor Euler product. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

theorem cubicThetaScalarEisenstein_residue {p : ℂ × ℝ} (hp : 0<p.2) :
    Tendsto (fun s : ℝ => ((s-2:ℝ):ℂ)*cubicThetaScalarEisenstein p (s:ℂ))
      (𝓝[>] 2) (𝓝 ((Real.pi:ℂ)^2/(54*principalIdealZeta 2))) := by
  have hf := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (cubicThetaFullHeightMass_residue hp)
  have hpcont := (cubicThetaPrimaryMass_continuousOn.continuousAt
    (Ioi_mem_nhds (by norm_num : (1:ℝ)<2))).tendsto.mono_left
      (show 𝓝[>] (2:ℝ)≤𝓝 2 from nhdsWithin_le_nhds)
  have hpC := Complex.continuous_ofReal.continuousAt.tendsto.comp hpcont
  have hp0 : (cubicThetaPrimaryMass 2:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaPrimaryMass_pos (by norm_num)).ne'
  have hd := hf.div hpC hp0
  have hval : ((4*Real.pi^2/243:ℝ):ℂ)/(cubicThetaPrimaryMass 2:ℂ)=
      (Real.pi:ℂ)^2/(54*principalIdealZeta 2) := by
    rw [cubicThetaPrimaryMass_two]
    push_cast
    ring
  rw [hval] at hd
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 2<s at hs
  change (((s-2)*cubicThetaFullHeightMass p s:ℝ):ℂ)/(cubicThetaPrimaryMass s:ℂ)=_
  rw [cubicThetaScalarEisenstein_ofReal hp,cubicThetaScalarHeightMass_eq_div hp hs]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
