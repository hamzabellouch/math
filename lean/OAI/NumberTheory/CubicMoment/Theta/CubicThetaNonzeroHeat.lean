import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualHeatBounds
import Mathlib.Analysis.MellinTransform

namespace OAI

/-! The nonzero Fourier heat integral is entire in the Eisenstein
parameter: its positive and reciprocal exponential factors control both
ends of the Mellin integral. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace CubicFirstMoment

def cubicThetaDoubleHeat (v A t : ℝ) : ℂ :=
  (Real.exp (-v^2*t-A/t):ℂ)

lemma cubicThetaDoubleHeat_continuous (v A : ℝ) :
    ContinuousOn (cubicThetaDoubleHeat v A) (Ioi 0) := by
  have h : ContinuousOn (fun t : ℝ => -v^2*t-A/t) (Ioi 0) :=
    (continuousOn_const.mul continuousOn_id).sub
      (continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht))
  exact Complex.continuous_ofReal.comp_continuousOn
    (Real.continuous_exp.comp_continuousOn h)

lemma cubicThetaDoubleHeat_top (v : ℝ) {A : ℝ} (hA : 0<A) :
    cubicThetaDoubleHeat v A =O[atTop] (fun t : ℝ => Real.exp (-v^2*t)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [cubicThetaDoubleHeat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul]
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (div_pos hA ht).le

lemma cubicThetaDoubleHeat_bottom (v : ℝ) {A : ℝ} (hA : 0<A) (b : ℝ) :
    cubicThetaDoubleHeat v A =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hA b).isBigO.comp_tendsto
    (tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop)
  change (fun t : ℝ => Real.exp (-A*t⁻¹)) =O[𝓝[>] 0] (fun t : ℝ => t⁻¹^b) at h
  have h' : (fun t : ℝ => Real.exp (-A/t)) =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
    simpa only [Function.comp_apply,div_eq_mul_inv,Real.rpow_neg_eq_inv_rpow] using h
  apply IsBigO.trans ?_ h'
  apply IsBigO.of_bound 1
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [cubicThetaDoubleHeat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul]
  apply Real.exp_le_exp.mpr
  have hpos : 0≤v^2*t := mul_nonneg (sq_nonneg _) (le_of_lt ht)
  rw [neg_div]
  nlinarith only [hpos]

lemma cubicThetaDoubleHeat_mellinConvergent {v A : ℝ} (hv : 0<v) (hA : 0<A)
    (s : ℂ) : MellinConvergent (cubicThetaDoubleHeat v A) s := by
  exact mellinConvergent_of_isBigO_rpow_exp (sq_pos_of_pos hv)
    ((cubicThetaDoubleHeat_continuous v A).locallyIntegrableOn measurableSet_Ioi)
    (cubicThetaDoubleHeat_top v hA) (cubicThetaDoubleHeat_bottom v hA (s.re-1))
    (by linarith)

lemma cubicThetaDoubleHeat_mellin_entire {v A : ℝ} (hv : 0<v) (hA : 0<A) :
    Differentiable ℂ (mellin (cubicThetaDoubleHeat v A)) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp (sq_pos_of_pos hv)
    ((cubicThetaDoubleHeat_continuous v A).locallyIntegrableOn measurableSet_Ioi)
    (cubicThetaDoubleHeat_top v hA) (cubicThetaDoubleHeat_bottom v hA (s.re-1))
    (by linarith)

lemma cubicThetaDualHeat_eq_mellin (v A : ℝ) (s : ℂ) :
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t)=
      mellin (cubicThetaDoubleHeat v A) (s-1) := by
  unfold mellin cubicThetaDualHeat cubicThetaDoubleHeat
  congr 1
  funext t
  simp only [smul_eq_mul,show s-1-1=s-2 by ring]

theorem cubicThetaNonzeroHeat_entire {v A : ℝ} (hv : 0<v) (hA : 0<A) :
    Differentiable ℂ (fun s : ℂ => ∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t) := by
  simp_rw [cubicThetaDualHeat_eq_mellin]
  exact (cubicThetaDoubleHeat_mellin_entire hv hA).comp (differentiable_id.sub_const 1)

end CubicFirstMoment

end

end OAI
