import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMetricScale
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusSmooth
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! The exact hyperbolic metric scaling of the derivative follows from the
proved two-point identity, by taking real directional secants. -/
noncomputable section
open Filter Topology
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicThetaMobius_derivative_scale (g : SL(2,ℂ)) {p : ℂ × ℝ}
    (hp : 0<p.2) (u : ℂ × ℝ) :
    cubicThetaRadius (fderiv ℝ (cubicThetaMobius g) p u)*p.2^2=
      cubicThetaRadius u*(cubicThetaMobius g p).2^2 := by
  let path : ℝ → ℂ × ℝ := fun t => p+t • u
  have hpath : HasDerivAt path u 0 := by
    change HasDerivAt (fun t : ℝ => p+t • u) u 0
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add p
  have hf := (cubicThetaMobius_contDiffAt g hp).differentiableAt (by norm_num)
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp [path])
  have hsec : Tendsto (fun t : ℝ => t⁻¹ • (cubicThetaMobius g (path t)-cubicThetaMobius g p))
      (𝓝[≠] 0) (𝓝 (fderiv ℝ (cubicThetaMobius g) p u)) := by
    simpa only [Function.comp_apply,zero_add,path,zero_smul,add_zero] using hd.tendsto_slope_zero
  have hheight : Tendsto (fun t => (path t).2) (𝓝[≠] (0:ℝ)) (𝓝 p.2) := by
    have hh := hpath.continuousAt.snd.tendsto
    simp only [path,zero_smul,add_zero] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have hheight' : Tendsto (fun t => (cubicThetaMobius g (path t)).2)
      (𝓝[≠] (0:ℝ)) (𝓝 (cubicThetaMobius g p).2) := by
    have hh := hd.continuousAt.snd.tendsto
    simp only [Function.comp_apply,path,zero_smul,add_zero] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have hleft := (cubicThetaRadius_continuous.continuousAt.tendsto.comp hsec).mul
    (hheight.mul (tendsto_const_nhds (x:=p.2)))
  have hright := (tendsto_const_nhds (x:=cubicThetaRadius u)).mul
    (hheight'.mul (tendsto_const_nhds (x:=(cubicThetaMobius g p).2)))
  have hpos : ∀ᶠ t in 𝓝 (0:ℝ), 0<(path t).2 := by
    exact hpath.continuousAt.snd.tendsto.eventually
      (Ioi_mem_nhds (by simpa only [path,zero_smul,add_zero] using hp))
  have he : (fun t : ℝ => cubicThetaRadius (t⁻¹ •
        (cubicThetaMobius g (path t)-cubicThetaMobius g p))*((path t).2*p.2)) =ᶠ[𝓝[≠] 0]
      (fun t => cubicThetaRadius u*((cubicThetaMobius g (path t)).2*(cubicThetaMobius g p).2)) := by
    filter_upwards [hpos.filter_mono inf_le_left,self_mem_nhdsWithin] with t ht ht0
    exact cubicThetaMobius_secant_scale g hp ht0 ht
  simpa only [pow_two] using tendsto_nhds_unique_of_eventuallyEq hleft hright he

end CubicFirstMoment

end

end OAI
