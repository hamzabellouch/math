import Mathlib
import OAI.Probability.SKSupport.Foundations.Cascade

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma hasDerivAt_varianceHeat_curve {g V X : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {s V' X' : ℝ}
    (hV : HasDerivAt V V' s) (hX : HasDerivAt X X' s) (hpos : 0 < V s) :
    HasDerivAt (fun r => varianceHeat (V r) g (X r))
      (V'/2*varianceHeat (V s) (deriv (deriv g)) (X s)+
        X'*varianceHeat (V s) (deriv g) (X s)) s := by
  have hrs : Real.sqrt (V s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hd := (hasFDerivAt_scaled_joint (hgc.of_le (by norm_num)) hg hg'
    (X s, Real.sqrt (V s))).comp_hasDerivAt s
    (hX.prodMk (hV.sqrt (ne_of_gt hpos)))
  have hs := (hasDerivAt_scaled (hgc.of_le (by norm_num)) hg hg'
    (Real.sqrt (V s)) (X s)).unique
    (hasDerivAt_scaled_second hgc hg hg' hg'' (Real.sqrt (V s)) (X s))
  convert hd using 1 <;> first | rfl | skip
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  rw [hs]
  dsimp only [varianceHeat]
  field_simp [hrs]
  ring

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma hasDerivAt_varianceLogHeat_curve {f V X : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ) {s V' X' : ℝ}
    (hV : HasDerivAt V V' s) (hX : HasDerivAt X X' s) (hpos : 0 < V s) :
    HasDerivAt (fun r => varianceLogHeat c (V r) f (X r))
      (V'*((1/2:ℝ)*deriv (deriv (varianceLogHeat c (V s) f)) (X s)+
        c/2*(deriv (varianceLogHeat c (V s) f) (X s))^2)+
        X'*deriv (varianceLogHeat c (V s) f) (X s)) s := by
  by_cases hc : c = 0
  · subst c
    obtain ⟨C,hC⟩ := hf.deriv_bounded.bound
    obtain ⟨D,hD⟩ := hf.deriv_bounded.deriv.bound
    have hfg := exponentialBound_of_lipschitz hLip
    have hfg' := ExponentialBound.of_bounded hC
    have hfg'' := ExponentialBound.of_bounded hD
    have hfc : ContDiff ℝ 2 f := hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have heF : varianceLogHeat 0 (V s) f = varianceHeat (V s) f := by funext z; simp [varianceLogHeat]
    rw [heF]
    simp only [varianceLogHeat, ↓reduceIte, zero_div, zero_mul, add_zero]
    rw [deriv_deriv_varianceHeat hfc hfg hfg' hfg'',
      deriv_varianceHeat (hfc.of_le (by norm_num)) hfg hfg']
    convert hasDerivAt_varianceHeat_curve hfc hfg hfg' hfg'' hV hX hpos using 1; ring
  · let g : ℝ → ℝ := fun z => Real.exp (c*f z)
    have hgc : ContDiff ℝ 2 g := ((contDiff_const.mul hf.smooth).exp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hg : ExponentialBound g := exponentialBound_exp hLip c
    have hg' : ExponentialBound (deriv g) := by
      simpa only [iteratedDeriv_one] using exponentialBound_exp_iteratedDeriv hf hLip c 1
    have hg'' : ExponentialBound (deriv (deriv g)) := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        exponentialBound_exp_iteratedDeriv hf hLip c 2
    have hq : varianceHeat (V s) g (X s) ≠ 0 := ne_of_gt (varianceHeat_exp_pos hLip c (V s) (X s))
    have hd := ((hasDerivAt_varianceHeat_curve hgc hg hg' hg'' hV hX hpos).log hq).div_const c
    have ht := (((hasDerivWithinAt_varianceHeat hgc hg hg' hg'' hpos.le (X s)).hasDerivAt
      (Ici_mem_nhds hpos)).log hq).div_const c
    have hteq : ((1/2:ℝ)*varianceHeat (V s) (deriv (deriv g)) (X s))/
        varianceHeat (V s) g (X s)/c =
        (1/2:ℝ)*deriv (deriv (varianceLogHeat c (V s) f)) (X s)+
          c/2*(deriv (varianceLogHeat c (V s) f) (X s))^2 := by
      apply ht.unique
      simpa only [varianceLogHeat, hc, ↓reduceIte, g] using
        (varianceLogHeat_equation hf hLip c hpos.le (X s)).hasDerivAt (Ici_mem_nhds hpos)
    have hs := ((hasDerivAt_scaled_space (hgc.of_le (by norm_num)) hg hg'
      (Real.sqrt (V s)) (X s)).log hq).div_const c
    have hseq : varianceHeat (V s) (deriv g) (X s)/varianceHeat (V s) g (X s)/c =
        deriv (varianceLogHeat c (V s) f) (X s) := by
      have heF : varianceLogHeat c (V s) f = fun z => Real.log (varianceHeat (V s) g z)/c := by
        funext z; simp only [varianceLogHeat,hc,↓reduceIte,g]
      rw [heF]
      exact hs.deriv.symm
    have hfun : (fun r => Real.log (varianceHeat (V r) g (X r))/c) =
        fun r => varianceLogHeat c (V r) f (X r) := by
      funext r; simp only [varianceLogHeat, hc, ↓reduceIte, g]
    rw [hfun] at hd
    apply hd.congr_deriv
    rw [← hteq, ← hseq]
    ring

end ZeroTemperatureSK.Heat
namespace ZeroTemperatureSK.Heat

def kernelConstant : ℝ := ∫ y : ℝ, |y| ∂gaussianReal 0 1

lemma kernelConstant_nonneg : 0 ≤ kernelConstant := integral_nonneg (fun _ => abs_nonneg _)

lemma integrable_standardGaussian_abs : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) := by
  simpa only [zero_mul, Real.exp_zero, mul_one] using integrable_abs_mul_exp_abs 0

lemma scaled_gradient_stein {g : ℝ → ℝ} (hg : BoundedSmooth g) (a x : ℝ) :
    a * deriv (scaled a g) x = ∫ y, y*g (x+a*y) ∂gaussianReal 0 1 := by
  obtain ⟨C,hC⟩ := hg.bound
  obtain ⟨D,hD⟩ := hg.deriv.bound
  have hgc : ContDiff ℝ 1 g := hg.smooth.of_le (by simp)
  rw [(hasDerivAt_scaled_space hgc (ExponentialBound.of_bounded hC)
    (ExponentialBound.of_bounded hD) a x).deriv]
  have he := standardGaussian_stein (g := fun y => g (x+a*y))
    (g' := fun y => a*deriv g (x+a*y)) (fun y => by
      convert (hgc.differentiable (by norm_num) (x+a*y)).hasDerivAt.comp y
        (((hasDerivAt_id y).const_mul a).const_add x) using 1 <;> first | rfl | ring)
    (integrable_scaled_of_expBound hg.smooth.continuous.measurable
      (ExponentialBound.of_bounded hC) a x)
    ((integrable_scaled_of_expBound hg.deriv.smooth.continuous.measurable
      (ExponentialBound.of_bounded hD) a x).const_mul a)
    (integrable_mul_scaled_of_expBound hg.smooth.continuous.measurable
      (ExponentialBound.of_bounded hC) a x)
  simpa only [integral_const_mul, scaled] using he.symm

lemma scaled_gradient_bound {g : ℝ → ℝ} (hg : BoundedSmooth g)
    {C : ℝ≥0} (hC : ∀ z, |g z| ≤ C) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (scaled a g) x| ≤ kernelConstant * C / a := by
  have he := scaled_gradient_stein hg a x
  have hi := integrable_mul_scaled_of_expBound hg.smooth.continuous.measurable
    (ExponentialBound.of_bounded hC) a x
  have hh : |a*deriv (scaled a g) x| ≤ kernelConstant*C := by
    rw [he]
    apply abs_integral_le_integral_abs.trans
    calc
      (∫ y, |y*g (x+a*y)| ∂gaussianReal 0 1) ≤
          ∫ y : ℝ, |y| *(C:ℝ) ∂gaussianReal 0 1 := by
        apply integral_mono hi.abs (integrable_standardGaussian_abs.mul_const C)
        intro y
        change |y*g (x+a*y)| ≤ |y| *(C:ℝ)
        rw [abs_mul]
        gcongr
        exact hC _
      _ = kernelConstant*C := by rw [integral_mul_const]; rfl
  rw [abs_mul, abs_of_pos ha] at hh
  apply (le_div_iff₀ ha).mpr
  linarith

lemma semigroup_gradient_bound {g : ℝ → ℝ} (hg : BoundedSmooth g)
    {C : ℝ≥0} (hC : ∀ z, |g z| ≤ C) {h : ℝ≥0} (hh : 0 < h) (x : ℝ) :
    |deriv (semigroup h g) x| ≤ kernelConstant * C / Real.sqrt (h:ℝ) := by
  have he : semigroup h g = scaled (Real.sqrt (h:ℝ)) g :=
    funext (fun z => semigroup_eq_scaled hg.smooth.continuous.measurable h z)
  rw [he]
  apply scaled_gradient_bound hg hC
  exact Real.sqrt_pos.mpr (by exact_mod_cast hh)

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
