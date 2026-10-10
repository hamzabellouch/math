import Mathlib
import OAI.Probability.SKValue.Gaussian.DensityDerivative

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SKValue
lemma ForwardDensityData.heat_pair_integrable (D:ForwardDensityData)
    {F:ℝ → ℝ} (hF:ExpGrowth F) (hm:Measurable F) (lam:ℝ) :
    Integrable (fun p:ℝ×ℝ ↦ D.weight p.2*F (p.2+lam*p.1)) (standardGaussian.prod volume) := by
  obtain ⟨a,C,ha,hC,hb⟩ := hF
  have he:ExpGrowth (fun x:ℝ ↦ C*Real.exp (a*|x|)) := by
    refine ⟨a,C,ha,hC,?_⟩
    intro x;rw [abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
  have hi:= (gaussian_exp_abs_integrable (a*|lam|)).mul_prod
    (D.weight_exp_integrable he (by fun_prop))
  apply hi.mono' ((D.weight_measurable.comp measurable_snd).mul (hm.comp (by fun_prop))).aestronglyMeasurable
  filter_upwards [] with p
  change ‖D.weight p.2*F (p.2+lam*p.1)‖≤_
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (D.weight_pos p.2)]
  have hh:=mul_le_mul_of_nonneg_left (expGrowth_shift_bound ha hC hb p.2 lam p.1) (D.weight_pos p.2).le
  convert! hh using 1
  ring

lemma ForwardDensityData.heat_duality (D:ForwardDensityData)
    {F:ℝ → ℝ} (hF:ExpGrowth F) (hm:Measurable F) (h:ℝ) :
    (∫ x,D.weight x*heat h F x)=(∫ x,heat h D.weight x*F x) := by
  let lam:=Real.sqrt h
  have hi:=D.heat_pair_integrable hF hm lam
  have hmp:MeasurePreserving (fun p:ℝ×ℝ ↦ (p.1,p.2-lam*p.1))
      (standardGaussian.prod volume) (standardGaussian.prod volume) := by
    apply (MeasurePreserving.id standardGaussian).skew_product
      (g:=fun z x:ℝ ↦ x-lam*z) (by fun_prop)
    exact ae_of_all _ (fun z ↦ map_sub_right_eq_self volume (lam*z))
  have hi':Integrable (fun p:ℝ×ℝ ↦ D.weight (p.2-lam*p.1)*F p.2) (standardGaussian.prod volume) := by
    convert! hmp.integrable_comp_of_integrable hi using 1
    funext p
    simp only [Function.comp_apply,sub_add_cancel]
  calc
    _ = ∫ x,∫ z,D.weight x*F (x+lam*z) ∂standardGaussian := by
      simp only [heat,lam,integral_const_mul]
    _ = ∫ z,(∫ x,D.weight x*F (x+lam*z)) ∂standardGaussian := (integral_integral_swap hi).symm
    _ = ∫ z,(∫ x,D.weight (x-lam*z)*F x) ∂standardGaussian := by
      apply integral_congr_ae
      filter_upwards [] with z
      have he:=integral_add_right_eq_self (μ:=volume) (fun x ↦ D.weight (x-lam*z)*F x) (lam*z)
      simpa only [add_sub_cancel_right] using he
    _ = ∫ x,∫ z,D.weight (x-lam*z)*F x ∂standardGaussian := integral_integral_swap hi'
    _ = ∫ x,heat h D.weight x*F x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_mul_const]
      congr 1
      change (∫ z,D.weight (x-lam*z) ∂standardGaussian)=∫ z,D.weight (x+lam*z) ∂standardGaussian
      rw [←gaussian_integral_neg (fun z ↦ D.weight (x+lam*z))]
      simp_rw [mul_neg,←sub_eq_add_neg]
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue
noncomputable def weightedJet (c : ℝ) (ψ f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | n+1 => fun x ↦ deriv (weightedJet c ψ f n) x+weightedJet c ψ f n x*(c*deriv ψ x)
lemma weightedJet_bounded {ψ f : ℝ → ℝ} (hψ : BoundedSmooth (deriv ψ))
    (hf : BoundedSmooth f) (c : ℝ) (n : ℕ) : BoundedSmooth (weightedJet c ψ f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.deriv.add (ih.mul (hψ.const_mul c))
lemma weighted_iteratedDeriv {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x ↦ Real.exp (c*ψ x)*f x)=
      fun x ↦ Real.exp (c*ψ x)*weightedJet c ψ f n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hd := hψ.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
    have hj := (weightedJet_bounded hψ.jets hf c n).smooth.differentiable
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
    convert! ((((hd x).hasDerivAt.const_mul c).exp).mul (hj x).hasDerivAt).deriv using 1
    dsimp [weightedJet]
    ring
lemma weighted_growth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0≤c) (n : ℕ) :
    ExpGrowth (iteratedDeriv n (fun x ↦ Real.exp (c*ψ x)*f x)) := by
  rw [weighted_iteratedDeriv hψ hf c n]
  obtain ⟨C,hC,hb⟩ := (weightedJet_bounded hψ.jets hf c n).bound_zero
  exact (ExpGrowth.exp_lipschitz hψ.lipschitz hc).mul_bounded hC hb

noncomputable def responseJet (c : ℝ) (ψ f : ℝ → ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  iteratedDeriv n (heat t (fun y ↦ Real.exp (c*ψ y)*f y)) x /
    heat t (fun y ↦ Real.exp (c*ψ y)) x
noncomputable def baseJet (c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  normalizedJet (fun t ↦ heat t (fun y ↦ Real.exp (c*ψ y))) n t x
lemma responseJet_continuous {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0≤c) (n : ℕ) :
    Continuous (fun p : ℝ×ℝ ↦ responseJet c ψ f n p.1 p.2) := by
  exact (heat_jet_continuous ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth)
    (weighted_growth hψ hf hc) n).div
    (heat_continuous (Real.continuous_exp.comp (continuous_const.mul hψ.smooth.continuous))
      (ExpGrowth.exp_lipschitz hψ.lipschitz hc))
    (fun p ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc p.2 (Real.sqrt p.1)).ne')
lemma responseJet_smooth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0≤c) (n : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (responseJet c ψ f n t) := by
  exact (smooth_iteratedDeriv
    (heat_contDiff ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth) (weighted_growth hψ hf hc) t) n).div
    (heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
      (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) t)
    (fun x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne')
lemma responseJet_space {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0≤c) (n : ℕ) (t x : ℝ) :
    HasDerivAt (responseJet c ψ f n t)
      (responseJet c ψ f (n+1) t x-responseJet c ψ f n t x*baseJet c ψ 1 t x) x := by
  have hnum := heat_contDiff ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth) (weighted_growth hψ hf hc) t
  have hden := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) t
  have hp := (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hd := (((hnum.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) x).hasDerivAt).div
    ((hden.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne') x).hasDerivAt hp
  convert! hd using 1
  dsimp only [responseJet,baseJet,normalizedJet]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  field_simp
lemma responseJet_time {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c t : ℝ} (hc : 0≤c) (ht : 0<t) (n : ℕ) (x : ℝ) :
    HasDerivAt (responseJet c ψ f n · x)
      ((1/2:ℝ)*(responseJet c ψ f (n+2) t x-responseJet c ψ f n t x*baseJet c ψ 2 t x)) t := by
  have hp := (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hd := (heat_jet_time ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth)
    (weighted_growth hψ hf hc) n x ht).div
      (heat_jet_time ((contDiff_const.mul hψ.smooth).exp)
        (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) 0 x ht) hp
  convert! hd using 1
  dsimp only [responseJet,baseJet,normalizedJet]
  simp only [iteratedDeriv_zero,zero_add]
  field_simp
lemma responseJet_bound {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0≤c) (n : ℕ) :
    ∃ C:ℝ,0≤C ∧ ∀ t x,|responseJet c ψ f n t x|≤C := by
  obtain ⟨C,hC,hb⟩ := (weightedJet_bounded hψ.jets hf c n).bound_zero
  refine ⟨C,hC,?_⟩
  intro t x
  have hs : ContDiff ℝ ∞ (fun y ↦ Real.exp (c*ψ y)*f y) := (contDiff_const.mul hψ.smooth).exp.mul hf.smooth
  have hp : 0<heat t (fun y ↦ Real.exp (c*ψ y)) x := lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)
  rw [responseJet,heat_iteratedDeriv hs (weighted_growth hψ hf hc),abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  apply heat_relative_bound ((Real.continuous_exp.comp (continuous_const.mul hψ.smooth.continuous)).measurable)
    (smooth_iteratedDeriv hs n).continuous.measurable (ExpGrowth.exp_lipschitz hψ.lipschitz hc)
    (weighted_growth hψ hf hc n)
  intro y
  rw [weighted_iteratedDeriv hψ hf c n,abs_mul,abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm,Function.comp_apply,Pi.mul_apply] using mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos (c*ψ y)).le
end SKValue

end

end OAI
