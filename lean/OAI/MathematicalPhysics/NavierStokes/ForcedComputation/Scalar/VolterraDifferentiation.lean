import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! The moving-endpoint part of differentiation of a Volterra integral. -/

noncomputable section
namespace ForcedComputation
open Set Filter MeasureTheory
open scoped Topology Interval

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Joint continuity is enough for the derivative of an integral over a shrinking
interval, even when its integrand depends on the moving endpoint. -/
theorem hasDerivAt_shrinking_integral (f : ℝ → ℝ → F)
    (hf : Continuous (Function.uncurry f)) (a : ℝ) :
    HasDerivAt (fun t => ∫ s in a..t, f t s) (f a a) a := by
  let g : ℝ → F := fun t => ∫ r in (0:ℝ)..1, f t (a+(t-a)*r)
  have hc : Continuous (fun p : ℝ × ℝ => f p.1 (a+(p.1-a)*p.2)) :=
    hf.comp (continuous_fst.prodMk
      (continuous_const.add ((continuous_fst.sub continuous_const).mul continuous_snd)))
  have hg : Continuous g :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t r => f t (a+(t-a)*r)) (μ := volume) hc 0 1
  have hg0 : g a = f a a := by
    simp [g]
  have he (t : ℝ) : (∫ s in a..t, f t s) = (t-a) • g t := by
    have h := intervalIntegral.smul_integral_comp_add_mul (f t) (t-a) a
      (a := (0:ℝ)) (b := 1)
    simpa only [mul_zero, add_zero, mul_one, add_sub_cancel] using h.symm
  apply hasDerivAt_iff_tendsto_slope.mpr
  have ht : Tendsto g (𝓝[≠] a) (𝓝 (f a a)) := by
    rw [← hg0]
    exact hg.continuousAt.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hta : t-a ≠ 0 := sub_ne_zero.mpr ht
  simp only [slope_def_module, he, sub_self, zero_smul, sub_zero,
    smul_smul, inv_mul_cancel₀ hta, one_smul]

/-- Leibniz' rule after the fixed-endpoint derivative has been justified by
dominated differentiation. -/
theorem hasDerivAt_volterra_of_fixed (f : ℝ → ℝ → F)
    (hf : Continuous (Function.uncurry f)) (a t : ℝ) (d : F)
    (hd : HasDerivAt (fun u => ∫ s in a..t, f u s) d t) :
    HasDerivAt (fun u => ∫ s in a..u, f u s) (d + f t t) t := by
  have hb := hasDerivAt_shrinking_integral F f hf t
  apply (hd.add hb).congr_of_eventuallyEq
  apply Eventually.of_forall
  intro u
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a t)
    ((hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable t u)).symm

end ForcedComputation

end

end OAI
