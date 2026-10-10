import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingEnergy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

namespace OAI

/-! Dominated strong differentiation for the line L2 functions used in
the sampling flow. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineLp_tendsto_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → ℝ → ℂ) (g : ℝ → ℂ) (hF : ∀ i, MemLp (F i) 2 volume)
    (hg : MemLp g 2 volume) (w : ℝ → ℝ)
    (hw : Integrable (fun y => w y^2))
    (hb : ∀ᶠ i in l, ∀ y, ‖F i y-g y‖≤w y)
    (hlim : ∀ y, Tendsto (fun i => F i y) l (𝓝 (g y))) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hg.toLp g)) := by
  have hint : Tendsto (fun i => ∫ y, ‖F i y-g y‖^2) l (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (F:=fun i y => ‖F i y-g y‖^2) (f:=fun _ => (0:ℝ)) (fun y => w y^2)
      (Eventually.of_forall fun i => ((hF i).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2)
      (by
        filter_upwards [hb] with i hi
        exact Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hi y) 2)
      hw (Eventually.of_forall fun y => by
        simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using
          ((hlim y).sub_const (g y)).norm.pow 2)
    simpa only [integral_zero] using hh
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF g hg).mpr
  have he (i : ι) : eLpNorm (F i-g) 2 volume=
      ENNReal.ofReal (Real.sqrt (∫ y, ‖F i y-g y‖^2)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) ((hF i).sub hg)]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp hint)
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using hh

theorem lineLp_hasDerivAt (F : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (t : ℝ)
    (hF : ∀ s, MemLp (F s) 2 volume) (hg : MemLp g 2 volume)
    (w : ℝ → ℝ) (hw : Integrable (fun y => w y^2))
    (hb : ∀ᶠ s in 𝓝[≠] t, ∀ y, ‖slope (fun r => F r y) t s-g y‖≤w y)
    (hd : ∀ y, HasDerivAt (fun s => F s y) (g y) t) :
    HasDerivAt (fun s => (hF s).toLp (F s)) (hg.toLp g) t := by
  let S := fun s y => slope (fun r => F r y) t s
  have hS (s : ℝ) : MemLp (S s) 2 volume :=
    ((hF s).sub (hF t)).const_smul (s-t)⁻¹
  have hlim := lineLp_tendsto_dominated S g hS hg w hw hb (fun y => (hd y).tendsto_slope)
  apply hasDerivAt_iff_tendsto_slope.mpr
  convert hlim using 1
  funext s
  change (s-t)⁻¹ • ((hF s).toLp (F s)-(hF t).toLp (F t))=(hS s).toLp (S s)
  rw [←MemLp.toLp_sub,←MemLp.toLp_const_smul]
  rfl

theorem lineLp_hasDerivAt_of_increment_bound (F : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (t : ℝ)
    (hF : ∀ s, MemLp (F s) 2 volume) (hg : MemLp g 2 volume)
    (w : ℝ → ℝ) (hw : Integrable (fun y => w y^2))
    (hb : ∀ᶠ s in 𝓝 t, ∀ y, ‖F s y-F t y‖≤|s-t| *w y)
    (hd : ∀ y, HasDerivAt (fun s => F s y) (g y) t) :
    HasDerivAt (fun s => (hF s).toLp (F s)) (hg.toLp g) t := by
  have hslope : ∀ᶠ s in 𝓝[≠] t, ∀ y, ‖slope (fun r => F r y) t s‖≤w y := by
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs hst y
    have hne : s-t≠0 := sub_ne_zero.mpr hst
    rw [slope_def_module,norm_smul,Real.norm_eq_abs,abs_inv]
    calc
      |s-t|⁻¹*‖F s y-F t y‖ ≤ |s-t|⁻¹*(|s-t| *w y) :=
        mul_le_mul_of_nonneg_left (hs y) (by positivity)
      _ = w y := by rw [←mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr hne),one_mul]
  have hg_bound (y : ℝ) : ‖g y‖≤w y :=
    le_of_tendsto (hd y).tendsto_slope.norm (hslope.mono fun _ hs => hs y)
  apply lineLp_hasDerivAt F g t hF hg (fun y => 2*w y)
  · simpa only [mul_pow,show (2:ℝ)^2=4 by norm_num] using hw.const_mul 4
  · filter_upwards [hslope] with s hs y
    exact (norm_sub_le _ _).trans (by linarith only [hs y,hg_bound y])
  · exact hd

end LipschitzHilbert.PacketRepresentation

end

end OAI
