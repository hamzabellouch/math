import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFSuffixSemigroup

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def standardGaussianAbsMoment : ℝ := ∫ z : ℝ, |z| ∂gaussianReal 0 1

theorem standardGaussianAbsMoment_nonneg : 0 ≤ standardGaussianAbsMoment :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem scalarStep_zero_mass_close {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hK : LipschitzWith K f) (v x : ℝ) :
    |scalarStep 0 v f x-f x| ≤ (K:ℝ)*|v| *standardGaussianAbsMoment := by
  let L : ℝ →L[ℝ] ℝ := v • ContinuousLinearMap.id ℝ ℝ
  have hf' : Integrable (fun z : ℝ => f (x+v*z)) (gaussianReal 0 1) :=
    ((hf.translate x).compCLM L).hasExpGrowth.integrable_gaussianMeasure
      (((hf.translate x).compCLM L).1.continuous)
  have hi : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
    simpa only [Real.norm_eq_abs] using
      (HasExpGrowth.norm_id (E:=ℝ)).integrable_gaussianMeasure continuous_norm (μ:=gaussianReal 0 1)
  simp only [scalarStep,gaussianStep,ite_true]
  have he : (∫ z : ℝ, f (x+v*z) ∂gaussianReal 0 1)-f x =
      ∫ z : ℝ, f (x+v*z)-f x ∂gaussianReal 0 1 := by
    rw [integral_sub hf' (integrable_const _)]; simp
  rw [he]
  calc
    _ ≤ ∫ z : ℝ, |f (x+v*z)-f x| ∂gaussianReal 0 1 := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z : ℝ => f (x+v*z)-f x) (μ:=gaussianReal 0 1)
    _ ≤ ∫ z : ℝ, (K:ℝ)*|v| *|z| ∂gaussianReal 0 1 := by
      apply integral_mono ((hf'.sub (integrable_const _)).norm) (hi.const_mul _)
      intro z
      have H := hK.dist_le_mul (x+v*z) x
      simpa only [Real.dist_eq,Real.norm_eq_abs,Pi.sub_apply,add_sub_cancel_left,abs_mul,mul_assoc] using H
    _ = _ := by rw [integral_const_mul]; rfl

theorem scalarCDFOperator_eq_zero_mass {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hK : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1)
    (hzero : ∀ z∈Ico s (s+t), α z=0) :
    scalarCDFOperator β α s t f=scalarTimeStep β 0 t f := by
  funext x
  exact scalarCDFOperator_eq_chain hf hK β ha hm [(0,t)]
    (by simp) s t ht (by simp [chainDuration]) ⟨hzero,trivial⟩ x

theorem scalarCDFOperator_small_time {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hK : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFOperator β α s t f x-f x| ≤
      scalarTimeMassConstantK β K*(t:ℝ)+(K:ℝ)*|β| *Real.sqrt (t:ℝ)*standardGaussianAbsMoment := by
  have h0 : ∀ z : ℝ, (0:ℝ)∈Icc (0:ℝ) 1 := by simp
  have H := scalarCDFOperator_cdf_lipschitz hf hK β ha hm h0 monotone_const s t ht x
  rw [scalarCDFOperator_eq_zero_mass hf hK β h0 monotone_const s t ht (by simp)] at H
  have hi : (∫ z in s..s+t, |α z-(0:ℝ)|) ≤ (t:ℝ) := by
    have hi' := intervalIntegral.integral_mono_on (show s ≤ s+(t:ℝ) from le_add_of_nonneg_right t.coe_nonneg)
      (hm.intervalIntegrable (μ:=volume)).abs (intervalIntegrable_const (c:=(1:ℝ)))
      (fun z _ => by simpa only [sub_zero,abs_of_nonneg (ha z).1] using (ha z).2)
    simpa only [sub_zero,intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,mul_one] using hi'
  have H' := scalarStep_zero_mass_close hf hK (β*Real.sqrt (t:ℝ)) x
  have he : |β*Real.sqrt (t:ℝ)|=|β| *Real.sqrt (t:ℝ) := by rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [he] at H'
  exact (abs_sub_le _ _ _).trans ((add_le_add (H.trans (mul_le_mul_of_nonneg_left hi
    (scalarTimeMassConstantK_nonneg β K))) H').trans_eq (by ring))

theorem scalarCDFValue_time_modulus (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : 0 ≤ s) (hsq : s ≤ q) (hq : q ≤ 1) (x : ℝ) :
    |scalarCDFValue β α s (Real.toNNReal (1-s)) x-
      scalarCDFValue β α q (Real.toNNReal (1-q)) x| ≤
      scalarTimeMassConstantK β 1*(q-s)+|β| *Real.sqrt (q-s)*standardGaussianAbsMoment := by
  have hr : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have ht : Real.toNNReal (q-s) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  rw [scalarCDFValue_suffix_semigroup β α ha h1 hs hsq hq]
  have H := scalarCDFOperator_small_time (scalarCDFValue_regular β ha α.mono q _ hr)
    (scalarCDFValue_lipschitz β ha α.mono q _ hr) β ha α.mono s _ ht x
  simpa only [Real.coe_toNNReal _ (sub_nonneg.mpr hsq),NNReal.coe_one,one_mul] using H

end SK.Analytic

end
end

end OAI
