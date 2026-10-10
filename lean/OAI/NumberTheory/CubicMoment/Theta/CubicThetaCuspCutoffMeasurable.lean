import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCutoffEnergy
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! Joint measurability of the true radial cusp derivative, needed to
integrate the sectionwise Hardy inequalities by Fubini. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspCutoffSection_continuous (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) :
    Continuous (Function.uncurry (cubicThetaCuspCutoffSection δ F)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  change ContinuousAt (fun y : ℂ × ℝ => cubicThetaCuspCutoff y.2*
    cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) y)) y
  by_cases hy : 0<y.2
  · have hpos := cubicThetaMobius_height_pos (cubicThetaFullComplex δ) hy
    have hf : ContinuousAt (cubicThetaSectionFunction F)
        (cubicThetaMobius (cubicThetaFullComplex δ) y) :=
      (F.property.1.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hpos)).continuousAt
    have hm := cubicThetaMobius_continuousAt (cubicThetaFullComplex δ) hy
    have hs := ContinuousAt.comp (f:=cubicThetaMobius (cubicThetaFullComplex δ))
      (g:=cubicThetaSectionFunction F) (x:=y) hf hm
    exact (cubicThetaCuspCutoff_smooth.continuous.continuousAt.comp continuous_snd.continuousAt).mul hs
  · have hlt : y.2<1 := lt_of_le_of_lt (le_of_not_gt hy) zero_lt_one
    have hnear : ∀ᶠ x : ℂ × ℝ in 𝓝 y, x.2<1 :=
      continuous_snd.continuousAt.eventually (eventually_lt_nhds hlt)
    have he : (fun y : ℂ × ℝ => cubicThetaCuspCutoff y.2*
        cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) y))=ᶠ[𝓝 y]
        (fun _ => (0:ℂ)) := by
      filter_upwards [hnear] with x hx
      rw [cubicThetaCuspCutoff_zero hx.le,zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq he

lemma cubicThetaCuspCutoff_deriv_measurable (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) :
    Measurable (fun y : ℂ × ℝ => deriv (cubicThetaCuspCutoffSection δ F y.1) y.2) :=
  measurable_deriv_with_param (cubicThetaCuspCutoffSection_continuous δ F)

end CubicFirstMoment

end

end OAI
