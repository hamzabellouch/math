import Mathlib
import OAI.Probability.SKValue.Control.Regularity

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def weightedEulerMoment (W : BrownianSpace) (γ η : OrderParameter)
    (T : ℝ) (N : ℕ) : ℝ :=
  stepSize T N*∑ j : Fin N,η.coeff (meshTime T N j)*
    (∫ z,(1/2 : ℝ)*(gradient W γ (meshTime T N j)
      (euler T N γ.coeff (gradient W γ) z j))^2 ∂gaussianProduct (Fin (N+1)))

lemma IsDiffusion.weightedEulerMoment_tendsto {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (η : OrderParameter)
    {T : ℝ} (hT : 0<T) (hT1 : T<1) :
    Tendsto (weightedEulerMoment W γ η T) atTop
      (𝓝 (∫ t in (0 : ℝ)..T,η.coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ))) := by
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := sourceStripRegularity W γ T ⟨hT.le,hT1⟩
  let E (N : ℕ) := ∫ ω,(meshMaxError T X (coupledEuler T γ.coeff (gradient W γ) W.B) N ω)^2 ∂W.μ
  let f (t : ℝ) := ∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ
  have hXM (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : MemLp (X t) 2 W.μ := hX.memLp ⟨ht.1,ht.2.trans hT1.le⟩ (by norm_num)
  have hpaths := hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ hu s hs t ht y x)
  have hEl : Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence W.brownian.toIsPreBrownianReal
    hT hG hLu hu (fun t ht ↦ (hXM t ht).aestronglyMeasurable) hpaths
  have hEs : Tendsto (fun N ↦ Real.sqrt (E N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hEl
  have hf : ContinuousOn f (Icc (0 : ℝ) T) := by
    have hc := (mean_derivative_square_continuous (by norm_num : (0 : ℝ)≤1) hLu
      (fun t ht ↦ (hG.smooth t ht).continuous) hG.bounded hu
      (fun t ht ↦ (hXM t ht).aestronglyMeasurable) (hpaths.mono (fun _ hω ↦ hω.1))).const_mul (1/2 : ℝ)
    simpa only [f,gradient,integral_const_mul] using hc
  have hfB (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : |f t|≤Kv := by
    simpa only [f,Real.norm_eq_abs,probReal_univ,mul_one] using
      (norm_integral_le_of_norm_le_const (μ := W.μ) (C := Kv)
        (f := fun ω ↦ (1/2 : ℝ)*(gradient W γ t (X t ω))^2)
        (Eventually.of_forall (fun ω ↦ by
          simpa only [Real.norm_eq_abs,gradient] using hV.product_bound t ht (X t ω))))
  apply perturbed_monotone_weighted_grid_tendsto (r := fun N ↦ Lv*Real.sqrt (E N)) hT hV.K_nonneg
    (η.monotone.mono (fun t ht ↦ ⟨ht.1,ht.2.trans_lt hT1⟩)) (η.nonneg 0 (by norm_num)) hf hfB
    (by simpa only [mul_zero] using hEs.const_mul Lv)
  filter_upwards [eventually_gt_atTop 0] with N hN j
  have hh := coupled_lipschitz_expectation_bound W.brownian.toIsPreBrownianReal hT hG
    (fun t ht ↦ hXM t ht) (hpaths.mono (fun _ hω ↦ hω.2.2)) hN j.isLt.le
    (hV.product_lipschitzWith (mesh_time_mem hT.le hN j.isLt.le))
  simpa only [Real.coe_toNNReal _ hV.L_nonneg,E,f,gradient] using hh

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma phi_difference_bound (W : BrownianSpace) (γ β : OrderParameter)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    |phi W β t x-phi W γ t x|≤(3/2 : ℝ)*(∫ s in t..1,|β.cutoff s-γ.cutoff s|) := by
  have hψ : LipschitzWith 1 (abs : ℝ → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub a b
  have hi (η : OrderParameter) : IntervalIntegrable (fun s ↦ η.cutoff (t+s)) volume 0 (1-t) := by
    simpa only [sub_self] using (η.cutoff_integrable.intervalIntegrable (a := t) (b := 1)).comp_add_left t
  have he := elapsedValue_difference_bound (f := shiftedFiltration W t)
    (brownian_increment_memLp W t) hψ hψ (fun y ↦ by simp : ∀ y : ℝ,|abs y-abs y|≤(0 : ℝ))
    (β.cutoff_measurable.comp (measurable_const.add measurable_id))
    (γ.cutoff_measurable.comp (measurable_const.add measurable_id)) (hi β) (hi γ)
    (sub_nonneg.mpr ht.2) (x := x)
  simp only [Function.comp_def,Pi.add_apply, id_eq] at he
  rw [←phi_eq_elapsedValue W β ht x,←phi_eq_elapsedValue W γ ht x] at he
  have hshift := intervalIntegral.integral_comp_add_left (fun s ↦ |β.cutoff s-γ.cutoff s|)
    (a := (0 : ℝ)) (b := 1-t) t
  simp only [add_zero,add_sub_cancel] at hshift
  rw [hshift] at he
  simpa only [zero_add] using he

lemma convex_derivative_uniform_comparison {f g : ℝ → ℝ} {L ε h : ℝ}
    (hf : ConvexOn ℝ univ f) (hg : ConvexOn ℝ univ g)
    (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g)
    (hL : ∀ x y,|deriv f x-deriv f y|≤L*|x-y|)
    (he : ∀ x,|g x-f x|≤ε) (hh : 0<h) (x : ℝ) :
    |deriv g x-deriv f x|≤L*h+2*ε/h := by
  have hp1 := hg.deriv_le_slope (mem_univ x) (mem_univ (x+h)) (by linarith) (hgd x)
  have hp2 := hf.slope_le_deriv (mem_univ x) (mem_univ (x+h)) (by linarith) (hfd (x+h))
  have hm1 := hg.slope_le_deriv (mem_univ (x-h)) (mem_univ x) (by linarith) (hgd x)
  have hm2 := hf.deriv_le_slope (mem_univ (x-h)) (mem_univ x) (by linarith) (hfd (x-h))
  rw [slope_def_field,show x+h-x=h by ring] at hp1 hp2
  rw [slope_def_field,show x-(x-h)=h by ring] at hm1 hm2
  have hp1' := (le_div_iff₀ hh).mp hp1
  have hp2' := (div_le_iff₀ hh).mp hp2
  have hm1' := (div_le_iff₀ hh).mp hm1
  have hm2' := (le_div_iff₀ hh).mp hm2
  have hpL := (le_abs_self _).trans (hL (x+h) x)
  have hmL := (neg_le_abs _).trans (hL (x-h) x)
  rw [show x+h-x=h by ring,abs_of_pos hh] at hpL
  rw [show x-h-x= -h by ring,abs_neg,abs_of_pos hh] at hmL
  have hpLm := mul_le_mul_of_nonneg_right hpL hh.le
  have hmLm := mul_le_mul_of_nonneg_right hmL hh.le
  have hx := (abs_le.mp (he x))
  have hxp := (abs_le.mp (he (x+h)))
  have hxm := (abs_le.mp (he (x-h)))
  have hcancel : (2*ε/h)*h=2*ε := div_mul_cancel₀ _ hh.ne'
  apply abs_le.mpr
  constructor <;> apply (mul_le_mul_iff_left₀ hh).mp <;> nlinarith

lemma phi_gradient_difference_bound (W : BrownianSpace) (γ β : OrderParameter)
    {T L ε h : ℝ} (hT : T∈Ico (0 : ℝ) 1)
    (hL : ∀ t∈Icc (0 : ℝ) T,∀ x y,|gradient W γ t x-gradient W γ t y|≤L*|x-y|)
    (he : ∀ t∈Icc (0 : ℝ) T,∀ x,|phi W β t x-phi W γ t x|≤ε)
    (hh : 0<h) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
    |gradient W β t x-gradient W γ t x|≤L*h+2*ε/h := by
  have ht1 : t∈Ico (0 : ℝ) 1 := ⟨ht.1,ht.2.trans_lt hT.2⟩
  exact convex_derivative_uniform_comparison (phi_convex W γ ⟨ht1.1,ht1.2.le⟩)
    (phi_convex W β ⟨ht1.1,ht1.2.le⟩)
    ((phi_smoothTerminal W γ ht1).smooth.differentiable (by simp))
    ((phi_smoothTerminal W β ht1).smooth.differentiable (by simp))
    (hL t ht) (he t ht) hh x

end SKValue

end

end OAI
