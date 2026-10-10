import Mathlib
import OAI.Probability.SKValue.Evolution.HeatContinuity

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma weighted_variance_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {w f : Ω → ℝ} (hw : ∀ x,0≤w x) (hZ : 0<∫ x,w x ∂μ)
    (hi : Integrable w μ) (hif : Integrable (fun x ↦ w x*f x) μ)
    (his : Integrable (fun x ↦ w x*(f x)^2) μ) :
    0≤(∫ x,w x ∂μ)*(∫ x,w x*(f x)^2 ∂μ)-(∫ x,w x*f x ∂μ)^2 := by
  let Z := ∫ x,w x ∂μ
  let A := ∫ x,w x*f x ∂μ
  let J := ∫ x,w x*(f x)^2 ∂μ
  let m := A/Z
  have hm : m*Z=A := div_mul_cancel₀ A hZ.ne'
  have hs : 0≤∫ x,w x*(f x-m)^2 ∂μ := integral_nonneg (fun x ↦ mul_nonneg (hw x) (sq_nonneg _))
  have he : (∫ x,w x*(f x-m)^2 ∂μ)=J-2*m*A+m^2*Z := by
    have hp : (fun x ↦ w x*(f x-m)^2)=
        fun x ↦ w x*(f x)^2-(2*m)*(w x*f x)+m^2*w x := by funext x; ring
    rw [hp]
    have hi1 : Integrable (fun x ↦ w x * f x ^ 2 - (2*m)*(w x*f x)) μ :=
      his.sub (hif.const_mul (2*m))
    rw [integral_add hi1 (hi.const_mul (m^2))]
    rw [integral_sub his (hif.const_mul (2*m))]
    simp only [integral_const_mul]
    rfl
  rw [he] at hs
  have hz := mul_nonneg hZ.le hs
  change 0≤Z*J-A^2
  have heq : Z*(J-2*m*A+m^2*Z)=Z*J-A^2 := by rw [←hm]; ring
  rwa [heq] at hz

lemma SmoothTerminal.coleHopf_curvature_pos {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hpos : ∀ x,0<deriv (deriv ψ) x) {c : ℝ} (hc : 0<c) (h x : ℝ) :
    0<deriv (deriv (coleHopf c h ψ)) x := by
  let f := fun y ↦ Real.exp (c*ψ y)
  let a := fun y ↦ c*deriv ψ y
  let b := fun y ↦ c*deriv (deriv ψ) y
  let f' := fun y ↦ f y*a y
  let f'' := fun y ↦ f y*((a y)^2+b y)
  have hψd := hψ.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hψ'd := hψ.jets.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have ha2c : Continuous (deriv (deriv ψ)) := hψ.jets.smooth.continuous_deriv
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hfd (y : ℝ) : HasDerivAt f (f' y) y := ((hψd y).hasDerivAt.const_mul c).exp
  have hf'd (y : ℝ) : HasDerivAt f' (f'' y) y := by
    have hd := (hfd y).mul ((hψ'd y).hasDerivAt.const_mul c)
    convert! hd using 1
    dsimp only [f,f',f'',a,b]
    ring
  have hfg : ExpGrowth f := ExpGrowth.exp_lipschitz hψ.lipschitz hc.le
  have hab (y : ℝ) : |a y|≤c := by
    have hh : |deriv ψ y|≤1 := by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ.lipschitz (x₀ := y)
    dsimp only [a]
    rw [abs_mul,abs_of_pos hc]
    nlinarith
  obtain ⟨K,hK,hKb⟩ := hψ.jets.bound 1
  have hbb (y : ℝ) : |b y|≤c*K := by
    dsimp only [b]
    rw [abs_mul,abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (by simpa only [iteratedDeriv_one] using hKb y) hc.le
  have hbg : ExpGrowth (fun y ↦ f y*b y) := hfg.mul_bounded (mul_nonneg hc.le hK) hbb
  have hag : ExpGrowth f' := hfg.mul_bounded hc.le hab
  have ha2b (y : ℝ) : |(a y)^2|≤c^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hc.le).mpr (hab y)
  have ha2g : ExpGrowth (fun y ↦ f y*(a y)^2) := hfg.mul_bounded (sq_nonneg c) ha2b
  have hf''g : ExpGrowth f'' := hfg.mul_bounded (add_nonneg (sq_nonneg c) (mul_nonneg hc.le hK))
    (fun y ↦ (abs_add_le _ _).trans (add_le_add (ha2b y) (hbb y)))
  have hfc : Continuous f := Real.continuous_exp.comp (continuous_const.mul hψ.smooth.continuous)
  have hac : Continuous a := continuous_const.mul hψ.jets.smooth.continuous
  have hbc : Continuous b := continuous_const.mul ha2c
  have hia := hag.shift_integrable (hfc.mul hac).measurable x (Real.sqrt h)
  have hia2 := ha2g.shift_integrable (hfc.mul (hac.pow 2)).measurable x (Real.sqrt h)
  have hib := hbg.shift_integrable (hfc.mul hbc).measurable x (Real.sqrt h)
  have hi := hfg.shift_integrable hfc.measurable x (Real.sqrt h)
  have hZ : 0<heat h f x := lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt h)
  have hvar := weighted_variance_nonneg
    (w := fun z ↦ f (x+Real.sqrt h*z)) (f := fun z ↦ a (x+Real.sqrt h*z))
    (fun z ↦ (Real.exp_pos _).le) hZ hi hia hia2
  have hbpos : ∀ z,0<f (x+Real.sqrt h*z)*b (x+Real.sqrt h*z) :=
    fun z ↦ mul_pos (Real.exp_pos _) (mul_pos hc (hpos _))
  have hKpos : 0<heat h (fun y ↦ f y*b y) x := by
    apply (integral_pos_iff_support_of_nonneg (fun z ↦ (hbpos z).le) hib).mpr
    have he : Function.support (fun z ↦ f (x+Real.sqrt h*z)*b (x+Real.sqrt h*z))=univ :=
      eq_univ_of_forall (fun z ↦ (hbpos z).ne')
    rw [he,measure_univ]
    norm_num
  have hsplit : heat h f'' x=heat h (fun y ↦ f y*(a y)^2) x+heat h (fun y ↦ f y*b y) x := by
    change (∫ z,f (x+Real.sqrt h*z)*((a (x+Real.sqrt h*z))^2+b (x+Real.sqrt h*z)) ∂standardGaussian)=_
    simp_rw [mul_add]
    exact integral_add hia2 hib
  have hp (y : ℝ) : heat h f y≠0 := (lipschitz_exp_integral_pos hψ.lipschitz hc.le y (Real.sqrt h)).ne'
  have heq : coleHopf c h ψ=fun y ↦ Real.log (heat h f y)/c := by
    funext y
    simp only [coleHopf,ite_eq_right hc.ne',f]
  rw [heq,heat_log_spatial_second hfd hf'd (hfc.mul ((hac.pow 2).add hbc)) hfg hag hf''g c h hp x]
  apply div_pos _ hc
  apply div_pos _ (sq_pos_of_pos hZ)
  rw [hsplit]
  change 0≤heat h f x*heat h (fun y ↦ f y*(a y)^2) x-(heat h f' x)^2 at hvar
  nlinarith [mul_pos hZ hKpos]

end SKValue

end

end OAI
