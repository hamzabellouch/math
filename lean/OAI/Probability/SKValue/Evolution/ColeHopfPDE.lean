import Mathlib
import OAI.Probability.SKValue.Evolution.HeatRegularity

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma heat_log_spatial_deriv {f f' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : Continuous f')
    (hfg : ExpGrowth f) (hf'g : ExpGrowth f') (c h : ℝ)
    (hp : ∀ x, heat h f x ≠ 0) :
    deriv (fun x ↦ Real.log (heat h f x)/c) = fun x ↦ (heat h f' x/heat h f x)/c := by
  funext x
  exact (((heat_spatial_hasDerivAt hf hf' hfg hf'g x h).log (hp x)).div_const c).deriv

lemma heat_log_spatial_second {f f' f'' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf'' : Continuous f'') (hfg : ExpGrowth f) (hf'g : ExpGrowth f')
    (hf''g : ExpGrowth f'') (c h : ℝ) (hp : ∀ x, heat h f x ≠ 0) (x : ℝ) :
    deriv (deriv (fun y ↦ Real.log (heat h f y)/c)) x =
      ((heat h f'' x*heat h f x-heat h f' x*heat h f' x)/(heat h f x)^2)/c := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr (fun y ↦ (hf' y).continuousAt)
  rw [heat_log_spatial_deriv hf hf'c hfg hf'g c h hp]
  exact (((heat_spatial_hasDerivAt hf' hf'' hf'g hf''g x h).div
    (heat_spatial_hasDerivAt hf hf'c hfg hf'g x h) (hp x)).div_const c).deriv

lemma heat_log_pde {f f' f'' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf'' : Continuous f'') (hfg : ExpGrowth f) (hf'g : ExpGrowth f')
    (hf''g : ExpGrowth f'') {c h : ℝ} (hc : c≠0) (hh : 0<h)
    (hp : ∀ x, heat h f x ≠ 0) (x : ℝ) :
    HasDerivAt (fun r ↦ Real.log (heat r f x)/c)
      ((1/2 : ℝ)*(deriv (deriv (fun y ↦ Real.log (heat h f y)/c)) x +
        c*(deriv (fun y ↦ Real.log (heat h f y)/c) x)^2)) h := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr (fun y ↦ (hf' y).continuousAt)
  have hd := ((heat_time_hasDerivAt hf hf' hf'' hfg hf'g hf''g x hh).log (hp x)).div_const c
  rw [heat_log_spatial_second hf hf' hf'' hfg hf'g hf''g c h hp,
    heat_log_spatial_deriv hf hf'c hfg hf'g c h hp]
  convert! hd using 1
  field_simp [hp x,hc]
  ring

lemma ExpGrowth.mul_bounded {f g : ℝ → ℝ} (hf : ExpGrowth f)
    {R : ℝ} (hR : 0≤R) (hg : ∀ x, |g x|≤R) : ExpGrowth (fun x ↦ f x*g x) := by
  obtain ⟨a,C,ha,hC,hf⟩ := hf
  refine ⟨a,C*R,ha,mul_nonneg hC hR,?_⟩
  intro x
  rw [abs_mul]
  calc
    _ ≤ (C*Real.exp (a* |x|))*R := mul_le_mul (hf x) (hg x) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma ExpGrowth.exp_lipschitz {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {c : ℝ} (hc : 0≤c) : ExpGrowth (fun x ↦ Real.exp (c*ψ x)) := by
  refine ⟨c,Real.exp (c*ψ 0),hc,(Real.exp_pos _).le,?_⟩
  intro x
  rw [abs_of_pos (Real.exp_pos _),←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := hψ.dist_le_mul x 0
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,sub_zero] at hh
  have hx := le_abs_self (ψ x-ψ 0)
  nlinarith

lemma coleHopf_pde_of_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c h : ℝ} (hc : 0<c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ coleHopf c r ψ x)
      ((1/2 : ℝ)*(deriv (deriv (coleHopf c h ψ)) x+c*(deriv (coleHopf c h ψ) x)^2)) h := by
  let f := fun x ↦ Real.exp (c*ψ x)
  let f' := fun x ↦ Real.exp (c*ψ x)*(c*deriv ψ x)
  let f'' := fun x ↦ Real.exp (c*ψ x)*((c*deriv ψ x)^2+c*deriv (deriv ψ) x)
  have hψd := hψs.differentiable (by norm_num)
  have hψ's : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψs).2.2
  have hψ'd : Differentiable ℝ (deriv ψ) := hψ's.differentiable (by norm_num)
  have hψc := hψs.continuous
  have hψ'c := hψs.continuous_deriv (by norm_num)
  have hψ''c : Continuous (deriv (deriv ψ)) :=
    hψ's.continuous_deriv (by norm_num)
  have hfd (y : ℝ) : HasDerivAt f (f' y) y := ((hψd y).hasDerivAt.const_mul c).exp
  have hf'd (y : ℝ) : HasDerivAt f' (f'' y) y := by
    have hd := (hfd y).mul ((hψ'd y).hasDerivAt.const_mul c)
    convert! hd using 1
    dsimp only [f,f',f'']
    ring
  have hfg : ExpGrowth f := ExpGrowth.exp_lipschitz hψ hc.le
  have hψ'b (y : ℝ) : |deriv ψ y|≤1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y)
  have hf'g : ExpGrowth f' := hfg.mul_bounded hc.le (fun y ↦ by
    simpa only [abs_mul,abs_of_pos hc,mul_one] using
      mul_le_mul_of_nonneg_left (hψ'b y) hc.le)
  have hf''g : ExpGrowth f'' := hfg.mul_bounded (R := c^2+c*K) (by positivity) (fun y ↦ by
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_pos hc]
    have hsq : (c*deriv ψ y)^2≤c^2 := by
      have h := sq_le_sq₀ (abs_nonneg (deriv ψ y)) zero_le_one |>.mpr (hψ'b y)
      rw [sq_abs] at h
      nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr h)]
    linarith [mul_le_mul_of_nonneg_left (hψ'' y) hc.le])
  have hp (y : ℝ) : heat h f y≠0 := (lipschitz_exp_integral_pos hψ hc.le y (Real.sqrt h)).ne'
  have hd := heat_log_pde hfd hf'd (by dsimp [f'']; fun_prop) hfg hf'g hf''g hc.ne' hh hp x
  have heq (r : ℝ) : coleHopf c r ψ = fun y ↦ Real.log (heat r f y)/c := by
    funext y
    simp only [coleHopf,ite_eq_right hc.ne',f]
  simp_rw [heq]
  exact hd

lemma ExpGrowth.of_bound {f : ℝ → ℝ} {C : ℝ} (hC : 0≤C) (hf : ∀ x, |f x|≤C) :
    ExpGrowth f := by
  refine ⟨0,C,le_rfl,hC,?_⟩
  intro x
  simpa only [zero_mul,Real.exp_zero,mul_one] using hf x

lemma ExpGrowth.lipschitz {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) : ExpGrowth ψ := by
  refine ⟨1,|ψ 0|+1,by norm_num,by positivity,?_⟩
  intro x
  have hh := hψ.dist_le_mul x 0
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,sub_zero] at hh
  have hu : |ψ x|≤|ψ 0|+|x| := by
    have hh2 := abs_add_le (ψ x-ψ 0) (ψ 0)
    rw [sub_add_cancel] at hh2
    linarith
  rw [one_mul]
  have he1 : 1≤Real.exp |x| := Real.one_le_exp (abs_nonneg x)
  have he2 : |x|≤Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  nlinarith [mul_le_mul_of_nonneg_left he1 (abs_nonneg (ψ 0))]

lemma coleHopf_pde {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c h : ℝ} (hc : 0≤c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ coleHopf c r ψ x)
      ((1/2 : ℝ)*(deriv (deriv (coleHopf c h ψ)) x+c*(deriv (coleHopf c h ψ) x)^2)) h := by
  rcases hc.eq_or_lt with rfl | hc
  · have hd (y : ℝ) := ((hψs.differentiable (by norm_num)) y).hasDerivAt
    have hψ's : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψs).2.2
    have hd' (y : ℝ) := ((hψ's.differentiable (by norm_num)) y).hasDerivAt
    have hψ'g : ExpGrowth (deriv ψ) := ExpGrowth.of_bound zero_le_one (fun y ↦ by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y))
    have hψ''g := ExpGrowth.of_bound hK hψ''
    have heq (r : ℝ) : coleHopf 0 r ψ = heat r ψ := by funext y; simp [coleHopf]
    have h1 : deriv (heat h ψ)=heat h (deriv ψ) := by
      funext y
      exact (heat_spatial_hasDerivAt hd hψ's.continuous (ExpGrowth.lipschitz hψ) hψ'g y h).deriv
    have h2 : deriv (heat h (deriv ψ))=heat h (deriv (deriv ψ)) := by
      funext y
      exact (heat_spatial_hasDerivAt hd' (hψ's.continuous_deriv (by norm_num)) hψ'g hψ''g y h).deriv
    simpa only [heq,h1,h2,zero_mul,add_zero] using
      heat_time_hasDerivAt hd hd' (hψ's.continuous_deriv (by norm_num))
        (ExpGrowth.lipschitz hψ) hψ'g hψ''g x hh
  · exact coleHopf_pde_of_pos hψ hψs hK hψ'' hc hh x

lemma coleHopf_backward_pde {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c b t : ℝ} (hc : 0≤c) (ht : t<b) (x : ℝ) :
    HasDerivAt (fun s ↦ coleHopf c (b-s) ψ x)
      (-(1/2 : ℝ)*(deriv (deriv (coleHopf c (b-t) ψ)) x+
        c*(deriv (coleHopf c (b-t) ψ) x)^2)) t := by
  have hd := (coleHopf_pde hψ hψs hK hψ'' hc (sub_pos.mpr ht) x).comp t
    ((hasDerivAt_const t b).sub (hasDerivAt_id t))
  convert! hd using 1
  simp only [zero_sub]
  ring

end SKValue

end

end OAI
