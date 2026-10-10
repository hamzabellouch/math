import Mathlib
import OAI.Probability.SKValue.Equations.CubicEnvelopeMean

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def heat (h : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, ψ (x+Real.sqrt h*z) ∂standardGaussian

noncomputable def coleHopf (c h : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  if c=0 then heat h ψ x else Real.log (heat h (fun y ↦ Real.exp (c*ψ y)) x)/c

lemma density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ -y^2/2) (-x) x := by
    have hh := ((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ)
    simpa only [Pi.pow_def,Pi.neg_def,id_eq,pow_one,show (2 : ℕ)-1=1 from rfl,
      Nat.cast_ofNat,mul_one,neg_div,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh
  have hd := h1.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
  convert hd using 1 <;> try rfl
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    ring

lemma density_mul_integrable {f : ℝ → ℝ} (hf : Integrable f standardGaussian) :
    Integrable (fun x ↦ gaussianPDFReal 0 1 x*f x) := by
  rw [standardGaussian,gaussianReal_of_var_ne_zero _ (by norm_num)] at hf
  have hh := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Eventually.of_forall (fun x ↦ gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).mp hf
  simpa only [toReal_gaussianPDF,smul_eq_mul] using hh

lemma gaussian_exp_abs_integrable (a : ℝ) :
    Integrable (fun z ↦ Real.exp (a* |z|)) standardGaussian := by
  have hi := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) a).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-a))
  apply hi.mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    linarith [Real.exp_pos (-a*z)]
  · rw [abs_of_nonpos hz]
    have hid : a*(-z)=(-a)*z := by ring
    rw [hid]
    linarith [Real.exp_pos (a*z)]

lemma lipschitz_exp_bound {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {c : ℝ} (hc : 0≤c) (x y z s : ℝ) :
    Real.exp (c*ψ (y+s*z)) ≤
      Real.exp (c*(ψ x+|y-x|+|s| * |z|)) := by
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hc
  have hh := hψ.dist_le_mul (y+s*z) x
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hh
  have ha : |y+s*z-x|≤|y-x|+|s| * |z| := by
    rw [show y+s*z-x = (y-x)+s*z by ring]
    simpa only [abs_mul] using abs_add_le (y-x) (s*z)
  have hb := le_abs_self (ψ (y+s*z)-ψ x)
  linarith

lemma lipschitz_exp_integrable {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {c : ℝ} (hc : 0≤c) (x s : ℝ) :
    Integrable (fun z ↦ Real.exp (c*ψ (x+s*z))) standardGaussian := by
  have hi := (gaussian_exp_abs_integrable (c* |s|)).const_mul (Real.exp (c*ψ x))
  have hψc := hψ.continuous
  apply hi.mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hh := lipschitz_exp_bound hψ hc x x z s
  simpa only [sub_self,abs_zero,add_zero,mul_add,Real.exp_add,mul_assoc] using hh

lemma lipschitz_exp_integral_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {c : ℝ} (hc : 0≤c) (x s : ℝ) :
    0 < ∫ z, Real.exp (c*ψ (x+s*z)) ∂standardGaussian :=
  integral_exp_pos (lipschitz_exp_integrable hψ hc x s)

lemma gaussian_stein_of_integrable {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hfi : Integrable f standardGaussian)
    (hf'i : Integrable f' standardGaussian)
    (hxfi : Integrable (fun x ↦ x*f x) standardGaussian) :
    (∫ x, x*f x ∂standardGaussian) = ∫ x, f' x ∂standardGaussian := by
  have hi1 : Integrable (fun x ↦ f x*(-x*gaussianPDFReal 0 1 x)) := by
    convert (density_mul_integrable hxfi).neg using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have hi2 : Integrable (fun x ↦ f' x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hf'i
  have hi3 : Integrable (fun x ↦ f x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hfi
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal 0 1) (u' := f') (v' := fun x ↦ -x*gaussianPDFReal 0 1 x)
    (fun x _ ↦ hf x) (fun x _ ↦ density_hasDerivAt x) hi1 hi2 hi3
  have hb : (∫ x, f x*(-x*gaussianPDFReal 0 1 x)) =
      -(∫ x, gaussianPDFReal 0 1 x*(x*f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by ring)
  rw [hb] at hibp
  have he : (∫ x, gaussianPDFReal 0 1 x*(x*f x)) =
      ∫ x, gaussianPDFReal 0 1 x*f' x := by
    exact neg_injective hibp |>.trans (by congr 1; funext x; ring)
  simpa only [standardGaussian,integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul] using he

lemma exponential_heat_hasDerivAt {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 1 ψ) {c : ℝ} (hc : 0≤c) (x s : ℝ) :
    HasDerivAt (fun y ↦ ∫ z, Real.exp (c*ψ (y+s*z)) ∂standardGaussian)
      (∫ z, Real.exp (c*ψ (x+s*z))*(c*deriv ψ (x+s*z)) ∂standardGaussian) x := by
  have hψc := hψ.continuous
  have hψ'c := hψs.continuous_deriv (by norm_num)
  have hψd := hψs.differentiable (by norm_num)
  let bd := fun z ↦ c*Real.exp (c*(ψ x+1))*Real.exp ((c* |s|)* |z|)
  have hbi : Integrable bd standardGaussian :=
    (gaussian_exp_abs_integrable (c* |s|)).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y z ↦ Real.exp (c*ψ (y+s*z)))
    (F' := fun y z ↦ Real.exp (c*ψ (y+s*z))*(c*deriv ψ (y+s*z)))
    (s := Metric.ball x 1) (bound := bd) (by exact Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall (fun y ↦ by fun_prop))
    (lipschitz_exp_integrable hψ hc x s) (by fun_prop) _ hbi _).2
  · filter_upwards [] with z
    intro y hy
    have hyd : |y-x|≤1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hy.le
    have hd : |deriv ψ (y+s*z)|≤1 := by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y+s*z)
    have hex := lipschitz_exp_bound hψ hc x y z s
    have hex' : Real.exp (c*ψ (y+s*z)) ≤
        Real.exp (c*(ψ x+1+|s| * |z|)) :=
      hex.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hc))
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_mul,abs_of_nonneg hc]
    calc
      _ ≤ Real.exp (c*ψ (y+s*z))*(c*1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hc) (Real.exp_pos _).le
      _ ≤ c*Real.exp (c*(ψ x+1+|s| * |z|)) := by
        simpa only [mul_one,one_mul,mul_comm c] using mul_le_mul_of_nonneg_left hex' hc
      _ = bd z := by simp only [bd,mul_add,Real.exp_add,mul_assoc]
  · filter_upwards [] with z
    intro y _
    have hh := (((hψd (y+s*z)).hasDerivAt.comp y ((hasDerivAt_id y).add_const (s*z))).const_mul c).exp
    simpa only [mul_one,Function.comp_def,id_eq] using hh

lemma lipschitz_heat_integrable {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) (x s : ℝ) :
    Integrable (fun z ↦ ψ (x+s*z)) standardGaussian := by
  have hz : Integrable (fun z : ℝ ↦ z) standardGaussian :=
    (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 1 (by norm_num)).integrable le_rfl
  have hψc := hψ.continuous
  apply ((integrable_const (|ψ 0|+|x|)).add (hz.abs.const_mul |s|)).mono' (by fun_prop)
  filter_upwards [] with z
  simp only [Real.norm_eq_abs,Pi.add_apply]
  have hh := hψ.dist_le_mul (x+s*z) 0
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,sub_zero] at hh
  have ha := abs_add_le (ψ (x+s*z)-ψ 0) (ψ 0)
  have hb := abs_add_le x (s*z)
  simp only [sub_add_cancel,abs_mul] at ha hb
  linarith

lemma heat_hasDerivAt {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 1 ψ) (x s : ℝ) :
    HasDerivAt (fun y ↦ ∫ z, ψ (y+s*z) ∂standardGaussian)
      (∫ z, deriv ψ (x+s*z) ∂standardGaussian) x := by
  have hψc := hψ.continuous
  have hψ'c := hψs.continuous_deriv (by norm_num)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y z ↦ ψ (y+s*z)) (F' := fun y z ↦ deriv ψ (y+s*z))
    (s := Set.univ) (bound := fun _ ↦ (1 : ℝ)) (by simp)
    (Eventually.of_forall (fun _ ↦ by fun_prop))
    (lipschitz_heat_integrable hψ x s) (by fun_prop) _ (integrable_const 1) _).2
  · exact Eventually.of_forall (fun _ _ _ ↦ norm_deriv_le_of_lipschitz hψ)
  · filter_upwards [] with z
    intro y _
    simpa only [Function.comp_def,id_eq,mul_one] using
      (((hψs.differentiable (by norm_num)) (y+s*z)).hasDerivAt.comp y
        ((hasDerivAt_id y).add_const (s*z)))

lemma coleHopf_hasDerivAt_of_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 1 ψ) {c : ℝ} (hc : 0<c) (h x : ℝ) :
    HasDerivAt (coleHopf c h ψ)
      ((∫ z, Real.exp (c*ψ (x+Real.sqrt h*z))*deriv ψ (x+Real.sqrt h*z) ∂standardGaussian)/
        heat h (fun y ↦ Real.exp (c*ψ y)) x) x := by
  have hp := lipschitz_exp_integral_pos hψ hc.le x (Real.sqrt h)
  have hh := ((exponential_heat_hasDerivAt hψ hψs hc.le x (Real.sqrt h)).log hp.ne').div_const c
  have hf : coleHopf c h ψ = fun y ↦
      Real.log (∫ z, Real.exp (c*ψ (y+Real.sqrt h*z)) ∂standardGaussian)/c := by
    funext y
    simp only [coleHopf,ite_eq_right hc.ne',heat]
  rw [hf]
  convert! hh using 1
  rw [show (fun z ↦ Real.exp (c*ψ (x+Real.sqrt h*z))*(c*deriv ψ (x+Real.sqrt h*z))) =
      fun z ↦ c*(Real.exp (c*ψ (x+Real.sqrt h*z))*deriv ψ (x+Real.sqrt h*z)) by
        funext z; ring, integral_const_mul]
  dsimp only [heat]
  field_simp [hc.ne',hp.ne']

lemma coleHopf_deriv_bound_of_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 1 ψ) {c : ℝ} (hc : 0<c) (h x : ℝ) :
    |deriv (coleHopf c h ψ) x|≤1 := by
  have hψ'c := hψs.continuous_deriv (by norm_num)
  have hψ' (y : ℝ) : |deriv ψ y|≤1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y)
  have hfi := lipschitz_exp_integrable hψ hc.le x (Real.sqrt h)
  have hf'i : Integrable (fun z ↦ Real.exp (c*ψ (x+Real.sqrt h*z))*deriv ψ (x+Real.sqrt h*z))
      standardGaussian := hfi.mul_bdd (by fun_prop)
        (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hψ' (x+Real.sqrt h*z)))
  have hib : |∫ z, Real.exp (c*ψ (x+Real.sqrt h*z))*deriv ψ (x+Real.sqrt h*z) ∂standardGaussian| ≤
      ∫ z, Real.exp (c*ψ (x+Real.sqrt h*z)) ∂standardGaussian := by
    apply abs_integral_le_integral_abs.trans
    apply integral_mono hf'i.abs hfi
    intro z
    simpa only [abs_mul,abs_of_pos (Real.exp_pos _),mul_one] using
      mul_le_mul_of_nonneg_left (hψ' (x+Real.sqrt h*z)) (Real.exp_pos _).le
  rw [(coleHopf_hasDerivAt_of_pos hψ hψs hc h x).deriv,abs_div,heat,
    abs_of_pos (lipschitz_exp_integral_pos hψ hc.le x (Real.sqrt h))]
  exact (div_le_one (lipschitz_exp_integral_pos hψ hc.le x (Real.sqrt h))).mpr hib

end SKValue

end

end OAI
