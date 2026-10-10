import Mathlib
import OAI.Probability.JammingConcavity.FiniteRowRecursion

namespace OAI

/-! Log Heat Calculus. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma log_heat_calculus {f f₁ f₂ : ℝ → ℝ → ℝ} {T a : ℝ} (ha : a ≠ 0)
    (hf : ∀ x, f T x ≠ 0)
    (hx : ∀ x, HasDerivAt (f T) (f₁ T x) x)
    (hxx : ∀ x, HasDerivAt (f₁ T) (f₂ T x) x)
    (ht : ∀ x, HasDerivAt (fun r => f r x) ((1/2:ℝ)*f₂ T x) T) :
    let g := fun (r x : ℝ) => (1/a)*Real.log (f r x)
    Differentiable ℝ (g T) ∧ Differentiable ℝ (deriv (g T)) ∧
    ∀ x, HasDerivAt (fun r => g r x)
      ((1/2:ℝ)*(deriv (deriv (g T)) x+a*(deriv (g T) x)^2)) T := by
  dsimp only
  let g := fun (r x : ℝ) => (1/a)*Real.log (f r x)
  have hg (x : ℝ) : HasDerivAt (g T) ((1/a)*(f₁ T x/f T x)) x :=
    ((hx x).log (hf x)).const_mul _
  have he : deriv (g T) = fun x => (1/a)*(f₁ T x/f T x) := funext fun x => (hg x).deriv
  have hg' (x : ℝ) : HasDerivAt (deriv (g T))
      ((1/a)*((f₂ T x*f T x-f₁ T x*f₁ T x)/(f T x)^2)) x := by
    rw [he]
    exact ((hxx x).div (hx x) (hf x)).const_mul _
  refine ⟨fun x => (hg x).differentiableAt, fun x => (hg' x).differentiableAt, fun x => ?_⟩
  have htime := ((ht x).log (hf x)).const_mul (1/a)
  have hi : (1/a)*(((1/2:ℝ)*f₂ T x)/f T x) =
      (1/2:ℝ)*(deriv (deriv (g T)) x+a*(deriv (g T) x)^2) := by
    rw [(hg' x).deriv, (hg x).deriv]
    field_simp [ha,hf x]
    ring
  rw [hi] at htime
  exact htime

lemma gaussianHeat_twice_calculus {v v' v'' : ℝ → ℝ}
    (hv : Measurable v) (hv' : Measurable v') (hv'' : Measurable v'')
    (hg : HeatQuadraticGrowth v) (hg' : HeatQuadraticGrowth v') (hg'' : HeatQuadraticGrowth v'')
    (hdv : ∀ x, HasDerivAt v (v' x) x) (hdv' : ∀ x, HasDerivAt v' (v'' x) x)
    {T : ℝ} (hT : 0 < T) :
    Differentiable ℝ (gaussianHeat v T) ∧ Differentiable ℝ (deriv (gaussianHeat v T)) ∧
    ∀ x, HasDerivAt (fun r => gaussianHeat v r x)
      ((1/2:ℝ)*deriv (deriv (gaussianHeat v T)) x) T := by
  have hx := gaussianHeat_space_derivative hv hv' hg hg' hdv T
  have hxx := gaussianHeat_space_derivative hv' hv'' hg' hg'' hdv' T
  have he : deriv (gaussianHeat v T) = gaussianHeat v' T := funext fun x => (hx x).deriv
  refine ⟨fun x => (hx x).differentiableAt, ?_, ?_⟩
  · rw [he]; exact fun x => (hxx x).differentiableAt
  · intro x
    rw [he,(hxx x).deriv]
    exact gaussianHeat_time_derivative hv hv' hv'' hg hg' hg'' hdv hdv' hT x
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma gaussianHeat_zero (v : ℝ → ℝ) (x : ℝ) : gaussianHeat v 0 x = v x := by
  simp [gaussianHeat]

lemma gaussianRowOperator_zero (a : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    gaussianRowOperator a 0 u x = u x := by
  by_cases ha : a=0
  · simp [gaussianRowOperator,ha,gaussianHeat_zero]
  · simp [gaussianRowOperator,ha,gaussianHeat_zero,Real.log_exp]

lemma gaussianRowOperator_calculus {u : ℝ → ℝ} {A B C κ Q a T : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (ha : 0 ≤ a) (hT : 0 < T) :
    Differentiable ℝ (gaussianRowOperator a T u) ∧
    Differentiable ℝ (deriv (gaussianRowOperator a T u)) ∧
    ∀ x, HasDerivAt (fun r => gaussianRowOperator a r u x)
      ((1/2:ℝ)*(deriv (deriv (gaussianRowOperator a T u)) x+
        a*(deriv (gaussianRowOperator a T u) x)^2)) T := by
  by_cases haz : a=0
  · subst a
    have hd := contDiff_infty_iff_deriv.mp hu.1
    have hd' := contDiff_infty_iff_deriv.mp hd.2
    have hh := gaussianHeat_twice_calculus hu.1.continuous.measurable
      hd.2.continuous.measurable hd'.2.continuous.measurable
      (row_terminal_quadratic_growth hu) (row_terminal_deriv_growth hu)
      (row_terminal_second_growth hu) (fun x => (hd.1 x).hasDerivAt)
      (fun x => (hd'.1 x).hasDerivAt) hT
    have he (r : ℝ) : gaussianRowOperator 0 r u = gaussianHeat u r := by
      funext x; simp [gaussianRowOperator]
    simpa only [he,zero_mul,add_zero] using hh
  · obtain ⟨hm,hm₁,hm₂⟩ := row_exp_measurable hu a
    obtain ⟨hg,hg₁,hg₂⟩ := row_exp_growth hu ha
    obtain ⟨hd,hd₁⟩ := row_exp_derivatives hu a
    have hp (x : ℝ) : 0 < gaussianHeat (fun y => Real.exp (a*u y)) T x :=
      integral_exp_pos (heat_affine_quadratic_integrable hm hg x (Real.sqrt T))
    have hh := log_heat_calculus haz (fun x => (hp x).ne')
      (gaussianHeat_space_derivative hm hm₁ hg hg₁ hd T)
      (gaussianHeat_space_derivative hm₁ hm₂ hg₁ hg₂ hd₁ T)
      (gaussianHeat_time_derivative hm hm₁ hm₂ hg hg₁ hg₂ hd hd₁ hT)
    have he (r : ℝ) : gaussianRowOperator a r u =
        fun x => (1/a)*Real.log (gaussianHeat (fun y => Real.exp (a*u y)) r x) := by
      funext x; simp only [gaussianRowOperator,ite_eq_right haz]
    simpa only [he] using hh

theorem gaussian_cole_hopf : GaussianColeHopfStatement := by
  intro u A B C κ Q hQ hu a ha ha1
  exact ⟨gaussianRowOperator_zero a u,fun T hT _ => gaussianRowOperator_calculus hu ha hT⟩
end MicroscopicJamming

 
 

namespace MicroscopicJamming

def GaussianCurvatureStatement : Prop :=
  ∀ (u : ℝ → ℝ) (A B C κ Q : ℝ), 0 < Q → RowAnalyticTerminal u A B C κ Q →
  ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ T : ℝ, 0 < T → T ≤ Q →
  ∀ x : ℝ, -C ≤ deriv (deriv (gaussianRowOperator a T u)) x ∧
    deriv (deriv (gaussianRowOperator a T u)) x ≤ κ/(1-κ*T)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma integral_four_linear {μ : Measure ℝ} {f g h k : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) (hk : Integrable k μ)
    (a b c d : ℝ) :
    (∫ x,a*f x-b*g x-c*h x+d*k x ∂μ) =
      a*(∫ x,f x ∂μ)-b*(∫ x,g x ∂μ)-c*(∫ x,h x ∂μ)+d*(∫ x,k x ∂μ) := by
  have hfg : Integrable (fun x => a*f x-b*g x) μ := (hf.const_mul a).sub (hg.const_mul b)
  have hfgh : Integrable (fun x => a*f x-b*g x-c*h x) μ := hfg.sub (hh.const_mul c)
  rw [integral_add hfgh (hk.const_mul d),integral_sub hfg (hh.const_mul c),
    integral_sub (hf.const_mul a) (hg.const_mul b),integral_const_mul,
    integral_const_mul,integral_const_mul,integral_const_mul]

lemma integral_three_linear {μ : Measure ℝ} {f g h : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) (a b c : ℝ) :
    (∫ x,a*f x-b*g x+c*h x ∂μ) =
      a*(∫ x,f x ∂μ)-b*(∫ x,g x ∂μ)+c*(∫ x,h x ∂μ) := by
  have hfg : Integrable (fun x => a*f x-b*g x) μ := (hf.const_mul a).sub (hg.const_mul b)
  rw [integral_add hfg (hh.const_mul c),integral_sub (hf.const_mul a) (hg.const_mul b),
    integral_const_mul,integral_const_mul,integral_const_mul]

lemma weighted_covariance_nonpos {μ : Measure ℝ} {f w : ℝ → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hf : Antitone f)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => x*w x) μ)
    (h2 : Integrable (fun x => f x*w x) μ)
    (h3 : Integrable (fun x => x*f x*w x) μ) :
    (∫ x,w x ∂μ)*(∫ x,x*f x*w x ∂μ) ≤
      (∫ x,f x*w x ∂μ)*(∫ x,x*w x ∂μ) := by
  let Z := ∫ x,w x ∂μ
  let L := ∫ x,x*w x ∂μ
  let U := ∫ x,f x*w x ∂μ
  let K := ∫ x,x*f x*w x ∂μ
  have hi (x : ℝ) : f x*x*Z-f x*L-x*U+K ≤ 0 := by
    have hh : (∫ y, ((f x*x)*w y-f x*(y*w y))-x*(f y*w y)+(y*f y*w y) ∂μ) ≤ 0 := by
      apply integral_nonpos_of_ae
      filter_upwards [] with y
      have hp : (f x-f y)*(x-y) ≤ 0 := by
        rcases le_total x y with hxy|hyx
        · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hf hxy)) (sub_nonpos.mpr hxy)
        · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hf hyx)) (sub_nonneg.mpr hyx)
      change ((f x*x)*w y-f x*(y*w y))-x*(f y*w y)+(y*f y*w y) ≤ 0
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hp (hw y)]
    have he := integral_four_linear h0 h1 h2 h3 (f x*x) (f x) x 1
    simp only [one_mul] at he
    rw [he] at hh
    exact hh
  have hh : (∫ x, Z*(x*f x*w x)-L*(f x*w x)-U*(x*w x)+K*w x ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [] with x
    change Z*(x*f x*w x)-L*(f x*w x)-U*(x*w x)+K*w x ≤ 0
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (hi x) (hw x)]
  rw [integral_four_linear h3 h2 h1 h0 Z L U K] at hh
  change Z*K ≤ U*L
  change Z*K-L*U-U*L+K*Z ≤ 0 at hh
  nlinarith

lemma weighted_covariance_upper {μ : Measure ℝ} {f w : ℝ → ℝ} {c : ℝ}
    (hw : ∀ x, 0 ≤ w x) (hf : Antitone (fun x => f x-c*x))
    (h0 : Integrable w μ) (h1 : Integrable (fun x => x*w x) μ)
    (h2 : Integrable (fun x => x^2*w x) μ)
    (hf0 : Integrable (fun x => f x*w x) μ)
    (hf1 : Integrable (fun x => x*f x*w x) μ) :
    (∫ x,w x ∂μ)*(∫ x,x*f x*w x ∂μ)-(∫ x,f x*w x ∂μ)*(∫ x,x*w x ∂μ) ≤
      c*((∫ x,w x ∂μ)*(∫ x,x^2*w x ∂μ)-(∫ x,x*w x ∂μ)^2) := by
  have he : (fun x => (f x-c*x)*w x) = fun x => f x*w x-c*(x*w x) := by funext x; ring
  have he' : (fun x => x*(f x-c*x)*w x) = fun x => x*f x*w x-c*(x^2*w x) := by funext x; ring
  have hg0 : Integrable (fun x => (f x-c*x)*w x) μ := by rw [he]; exact hf0.sub (h1.const_mul c)
  have hg1 : Integrable (fun x => x*(f x-c*x)*w x) μ := by rw [he']; exact hf1.sub (h2.const_mul c)
  have hh := weighted_covariance_nonpos hw hf h0 h1 hg0 hg1
  rw [he,he',integral_sub hf1 (h2.const_mul c),integral_sub hf0 (h1.const_mul c),
    integral_const_mul,integral_const_mul] at hh
  nlinarith only [hh]

lemma weighted_variance_nonneg {μ : Measure ℝ} {f w : ℝ → ℝ}
    (hw : ∀ x, 0 ≤ w x) (h0 : Integrable w μ)
    (h1 : Integrable (fun x => f x*w x) μ) (h2 : Integrable (fun x => (f x)^2*w x) μ)
    (hZ : 0 < ∫ x,w x ∂μ) :
    (∫ x,f x*w x ∂μ)^2 ≤ (∫ x,w x ∂μ)*(∫ x,(f x)^2*w x ∂μ) := by
  let Z := ∫ x,w x ∂μ
  let U := ∫ x,f x*w x ∂μ
  let K := ∫ x,(f x)^2*w x ∂μ
  have hh : 0 ≤ ∫ x, Z^2*((f x)^2*w x)-(2*Z*U)*(f x*w x)+U^2*w x ∂μ := by
    apply integral_nonneg
    intro x
    change 0 ≤ Z^2*((f x)^2*w x)-(2*Z*U)*(f x*w x)+U^2*w x
    nlinarith [mul_nonneg (sq_nonneg (Z*f x-U)) (hw x)]
  rw [integral_three_linear h2 h1 h0 (Z^2) (2*Z*U) (U^2)] at hh
  change 0 ≤ Z^2*K-(2*Z*U)*U+U^2*Z at hh
  change 0 < Z at hZ
  change U^2 ≤ Z*K
  nlinarith [mul_pos hZ (by positivity : 0 < Z)]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma gaussian_weighted_poly_integrable {f w : ℝ → ℝ} (hf : Measurable f) (hw : Measurable w)
    {D M : ℝ} (hD : 0 ≤ D) (_hM : 0 ≤ M) (n : ℕ)
    (hb : ∀ z, |f z| ≤ D*(1+|z|)^n) (hwM : ∀ z, |w z| ≤ M) :
    Integrable (fun z => f z*w z) (gaussianReal 0 1) := by
  apply ((gaussian_abs_one_pow_integrable n).const_mul (D*M)).mono' (hf.mul hw).aestronglyMeasurable
  filter_upwards [] with z
  change |f z*w z| ≤ _
  rw [abs_mul]
  calc
    |f z| * |w z| ≤ (D*(1+|z|)^n)*M := mul_le_mul (hb z) (hwM z) (abs_nonneg _) (by positivity)
    _ = _ := by ring

structure GaussianRowMoments (u : ℝ → ℝ) (a x b : ℝ) : Prop where
  zero : Integrable (fun z => Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  first : Integrable (fun z => z*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  second : Integrable (fun z => z^2*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  slope : Integrable (fun z => deriv u (x+b*z)*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  slope_first : Integrable (fun z => z*deriv u (x+b*z)*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  slope_sq : Integrable (fun z => (deriv u (x+b*z))^2*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  curvature : Integrable (fun z => deriv (deriv u) (x+b*z)*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)

lemma gaussianRowMoments {u : ℝ → ℝ} {A B C κ Q a : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (ha : 0 ≤ a) (x b : ℝ) : GaussianRowMoments u a x b := by
  obtain ⟨L,hL,hlin⟩ := row_terminal_deriv_linear hu
  let K := L*(1+|x|+|b|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound (z : ℝ) : |deriv u (x+b*z)| ≤ K*(1+|z|) := by
    exact (hlin _).trans (by dsimp [K]; nlinarith [mul_le_mul_of_nonneg_left (heat_affine_bound x b z) hL])
  have hb (z : ℝ) : |deriv (deriv u) (x+b*z)| ≤ C+κ := by
    rw [abs_le]; have hh := hu.2.2.2.2.2.2 (x+b*z)
    constructor <;> linarith [hh.2.2.1,hh.2.2.2,hu.2.2.1,hu.2.2.2.1]
  have h0 := hu.1.continuous.measurable
  have h1 := (contDiff_infty_iff_deriv.mp hu.1).2.continuous.measurable
  have h2 := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hu.1).2).2.continuous.measurable
  have hw : Measurable (fun z => Real.exp (a*u (x+b*z))) := by fun_prop
  have hwM (z : ℝ) : |Real.exp (a*u (x+b*z))| ≤ Real.exp (a*B) := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hu.2.2.2.2.2.2 _).2.1 ha)
  have hi {f : ℝ → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (n : ℕ)
      (hd : ∀ z, |f z| ≤ D*(1+|z|)^n) :=
    gaussian_weighted_poly_integrable hf hw hD (Real.exp_pos (a*B)).le n hd hwM
  constructor
  · have hh := hi (f := fun _ => (1:ℝ)) measurable_const (D := 1) (by norm_num) 0 (fun z => by norm_num)
    simpa using hh
  · exact hi measurable_id (D := 1) (by norm_num) 1 (fun z => by simp)
  · refine hi (by fun_prop) (D := 1) (by norm_num) 2 (fun z => ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg z,sq_abs z]
  · exact hi (by fun_prop) hK 1 (fun z => by simpa using hbound z)
  · refine hi (by fun_prop) hK 2 (fun z => ?_)
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left (hbound z) (abs_nonneg z)
    have hh' := mul_le_mul_of_nonneg_left (show |z| ≤ 1+|z| by linarith) (show 0 ≤ K*(1+|z|) by positivity)
    nlinarith
  · refine hi (by fun_prop) (sq_nonneg K) 2 (fun z => ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    have hh := pow_le_pow_left₀ (abs_nonneg (deriv u (x+b*z))) (hbound z) 2
    rw [sq_abs] at hh
    nlinarith only [hh]
  · exact hi (by fun_prop) (add_nonneg hu.2.2.1 hu.2.2.2.1) 0 (fun z => by simpa using hb z)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma row_gaussian_stein {u : ℝ → ℝ} {A B C κ Q a : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (ha : 0 ≤ a) (x b : ℝ) :
    let w := fun z => Real.exp (a*u (x+b*z))
    (∫ z,z*w z ∂gaussianReal 0 1) = a*b*(∫ z,deriv u (x+b*z)*w z ∂gaussianReal 0 1) ∧
    (∫ z,z*deriv u (x+b*z)*w z ∂gaussianReal 0 1) =
      b*(∫ z,deriv (deriv u) (x+b*z)*w z ∂gaussianReal 0 1)+
      a*b*(∫ z,(deriv u (x+b*z))^2*w z ∂gaussianReal 0 1) ∧
    (∫ z,z^2*w z ∂gaussianReal 0 1) = (∫ z,w z ∂gaussianReal 0 1)+
      a*b*(∫ z,z*deriv u (x+b*z)*w z ∂gaussianReal 0 1) := by
  dsimp only
  let w := fun z => Real.exp (a*u (x+b*z))
  have h := gaussianRowMoments hu ha x b
  obtain ⟨hdu,hcu'⟩ := contDiff_infty_iff_deriv.mp hu.1
  have hdu' := (contDiff_infty_iff_deriv.mp hcu').1
  have hy (z : ℝ) : HasDerivAt (fun r => x+b*r) b z := by
    convert (hasDerivAt_const z x).add ((hasDerivAt_id z).const_mul b) using 1 <;> first | rfl | simp
  have hw (z : ℝ) : HasDerivAt w (a*b*(deriv u (x+b*z)*w z)) z := by
    convert ((((hdu _).hasDerivAt.comp z (hy z)).const_mul a).exp) using 1 <;> first | rfl | (simp only [w,Function.comp_apply]; ring)
  have hs (z : ℝ) : HasDerivAt (fun r => deriv u (x+b*r)*w r)
      (b*(deriv (deriv u) (x+b*z)*w z)+a*b*((deriv u (x+b*z))^2*w z)) z := by
    convert (((hdu' _).hasDerivAt.comp z (hy z)).mul (hw z)) using 1 <;> first | rfl | (simp only [Function.comp_apply]; ring)
  have hz (z : ℝ) : HasDerivAt (fun r => r*w r)
      (w z+a*b*(z*deriv u (x+b*z)*w z)) z := by
    convert (hasDerivAt_id z).mul (hw z) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  constructor
  · have hh := standardGaussian_integration_by_parts hw h.zero (h.slope.const_mul (a*b)) h.first
    rw [integral_const_mul] at hh
    exact hh
  constructor
  · have hi : Integrable (fun z => z*(deriv u (x+b*z)*w z)) (gaussianReal 0 1) := by
      simpa only [mul_assoc] using h.slope_first
    have hh := standardGaussian_integration_by_parts hs h.slope
      ((h.curvature.const_mul b).add (h.slope_sq.const_mul (a*b))) hi
    rw [integral_add (h.curvature.const_mul b) (h.slope_sq.const_mul (a*b)),
      integral_const_mul,integral_const_mul] at hh
    simpa only [mul_assoc] using hh
  · have hi : Integrable (fun z => z*(z*w z)) (gaussianReal 0 1) := by
      convert h.second using 1; funext z; dsimp [w]; ring
    have hh := standardGaussian_integration_by_parts hz h.first
      (h.zero.add (h.slope_first.const_mul (a*b))) hi
    rw [integral_add h.zero (h.slope_first.const_mul (a*b)),integral_const_mul] at hh
    convert hh using 1
    congr 1; funext z; ring
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma gaussianRowOperator_second_exp {u : ℝ → ℝ} {A B C κ Q a : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (ha : 0 ≤ a) (haz : a ≠ 0) (T x : ℝ) :
    deriv (deriv (gaussianRowOperator a T u)) x =
      (1/a)*((gaussianHeat (rowExpSecond a u) T x * gaussianHeat (fun y => Real.exp (a*u y)) T x -
       (gaussianHeat (rowExpFirst a u) T x)^2)/(gaussianHeat (fun y => Real.exp (a*u y)) T x)^2) := by
  obtain ⟨hm,hm₁,hm₂⟩ := row_exp_measurable hu a
  obtain ⟨hg,hg₁,hg₂⟩ := row_exp_growth hu ha
  obtain ⟨hd,hd₁⟩ := row_exp_derivatives hu a
  have hp (y : ℝ) : gaussianHeat (fun z => Real.exp (a*u z)) T y ≠ 0 :=
    (integral_exp_pos (heat_affine_quadratic_integrable hm hg y (Real.sqrt T))).ne'
  have hx := gaussianHeat_space_derivative hm hm₁ hg hg₁ hd T
  have hxx := gaussianHeat_space_derivative hm₁ hm₂ hg₁ hg₂ hd₁ T
  have he : gaussianRowOperator a T u =
      fun y => (1/a)*Real.log (gaussianHeat (fun z => Real.exp (a*u z)) T y) := by
    funext y; simp only [gaussianRowOperator,ite_eq_right haz]
  have hdg (y : ℝ) : HasDerivAt (gaussianRowOperator a T u)
      ((1/a)*(gaussianHeat (rowExpFirst a u) T y/gaussianHeat (fun z => Real.exp (a*u z)) T y)) y := by
    rw [he]; exact ((hx y).log (hp y)).const_mul _
  have hdge : deriv (gaussianRowOperator a T u) =
      fun y => (1/a)*(gaussianHeat (rowExpFirst a u) T y/gaussianHeat (fun z => Real.exp (a*u z)) T y) :=
    funext fun y => (hdg y).deriv
  rw [hdge]
  have hh := (((hxx x).div (hx x) (hp x)).const_mul (1/a)).deriv
  convert hh using 1
  first | rfl | simp only [pow_two]

lemma gaussianRowOperator_second_moments {u : ℝ → ℝ} {A B C κ Q a : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (ha : 0 ≤ a) (haz : a ≠ 0) (T x : ℝ) :
    let w := fun z => Real.exp (a*u (x+Real.sqrt T*z))
    let Z := ∫ z,w z ∂gaussianReal 0 1
    let U := ∫ z,deriv u (x+Real.sqrt T*z)*w z ∂gaussianReal 0 1
    let V := ∫ z,(deriv u (x+Real.sqrt T*z))^2*w z ∂gaussianReal 0 1
    let J := ∫ z,deriv (deriv u) (x+Real.sqrt T*z)*w z ∂gaussianReal 0 1
    deriv (deriv (gaussianRowOperator a T u)) x = J/Z+a*(V/Z-(U/Z)^2) := by
  dsimp only
  have h := gaussianRowMoments hu ha x (Real.sqrt T)
  have hZ : (∫ z,Real.exp (a*u (x+Real.sqrt T*z)) ∂gaussianReal 0 1) ≠ 0 :=
    (integral_exp_pos h.zero).ne'
  have hfirst : gaussianHeat (rowExpFirst a u) T x =
      a*(∫ z,deriv u (x+Real.sqrt T*z)*Real.exp (a*u (x+Real.sqrt T*z)) ∂gaussianReal 0 1) := by
    rw [← integral_const_mul]
    unfold gaussianHeat rowExpFirst
    congr 1; funext z; ring
  have hsecond : gaussianHeat (rowExpSecond a u) T x =
      a*(∫ z,deriv (deriv u) (x+Real.sqrt T*z)*Real.exp (a*u (x+Real.sqrt T*z)) ∂gaussianReal 0 1)+
      a^2*(∫ z,(deriv u (x+Real.sqrt T*z))^2*Real.exp (a*u (x+Real.sqrt T*z)) ∂gaussianReal 0 1) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add (h.curvature.const_mul a) (h.slope_sq.const_mul (a^2))]
    unfold gaussianHeat rowExpSecond
    congr 1; funext z; ring
  rw [gaussianRowOperator_second_exp hu ha haz T x,hfirst,hsecond]
  unfold gaussianHeat
  field_simp [haz,hZ]
  ring
end MicroscopicJamming

 

namespace MicroscopicJamming
lemma row_curvature_algebra {a b C κ Z U V J L K S D : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 < b) (hκ : 0 ≤ κ) (hκb : κ*b^2 < 1)
    (hZ : 0 < Z) (hJ : -C*Z ≤ J) (hvar : U^2 ≤ Z*V)
    (hL : L=a*b*U) (hK : K=b*J+a*b*V) (hS : S=Z+a*b*K)
    (hcov : Z*K-U*L ≤ (κ*b)*(Z*S-L^2))
    (hD : D=J/Z+a*(V/Z-(U/Z)^2)) :
    -C ≤ D ∧ D ≤ κ/(1-κ*b^2) := by
  have hZ2 : 0 < Z^2 := sq_pos_of_pos hZ
  have he : D*Z^2 = J*Z+a*(V*Z-U^2) := by
    rw [hD]; field_simp [hZ.ne']
  have hX : Z*K-U*L = b*(D*Z^2) := by
    rw [he,hL,hK]; ring
  have hY : Z*S-L^2 = Z^2+a*b^2*(D*Z^2) := by
    rw [he,hS,hK,hL]; ring
  rw [hX,hY] at hcov
  have hc : D*Z^2 ≤ κ*(Z^2+a*b^2*(D*Z^2)) := by
    apply (mul_le_mul_iff_right₀ hb).mp
    nlinarith only [hcov]
  have hden : 0 < 1-a*κ*b^2 := by
    have hh := mul_le_mul_of_nonneg_right ha1 (mul_nonneg hκ (sq_nonneg b))
    nlinarith
  have hden' : 0 < 1-κ*b^2 := by linarith
  constructor
  · have hp := mul_le_mul_of_nonneg_right hJ hZ.le
    have hv := mul_nonneg ha (sub_nonneg.mpr hvar)
    nlinarith
  · have hD' : D*(1-a*κ*b^2) ≤ κ := by
      apply (mul_le_mul_iff_left₀ hZ2).mp
      nlinarith only [hc]
    apply ((le_div_iff₀ hden).mpr hD').trans
    apply div_le_div_of_nonneg_left hκ hden' (by
      have hh := mul_le_mul_of_nonneg_right ha1 (mul_nonneg hκ (sq_nonneg b)); nlinarith)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma row_slope_antitone {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (x : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    Antitone (fun z => deriv u (x+b*z)-(κ*b)*z) := by
  obtain ⟨_,hcu⟩ := contDiff_infty_iff_deriv.mp hu.1
  have hd := (contDiff_infty_iff_deriv.mp hcu).1
  have hh (z : ℝ) : HasDerivAt (fun r => deriv u (x+b*r)-(κ*b)*r)
      (deriv (deriv u) (x+b*z)*b-κ*b) z := by
    have hy : HasDerivAt (fun r : ℝ => x+b*r) b z := by
      convert (hasDerivAt_const z x).add ((hasDerivAt_id z).const_mul b) using 1 <;> first | rfl | simp
    convert ((hd _).hasDerivAt.comp z hy).sub ((hasDerivAt_id z).const_mul (κ*b)) using 1 <;> first | rfl | simp
  apply antitone_of_deriv_nonpos (fun z => (hh z).differentiableAt)
  intro z
  rw [(hh z).deriv]
  exact sub_nonpos.mpr (mul_le_mul_of_nonneg_right (hu.2.2.2.2.2.2 _).2.2.2 hb)

lemma gaussianRowOperator_second_zero {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (T x : ℝ) :
    deriv (deriv (gaussianRowOperator 0 T u)) x = gaussianHeat (deriv (deriv u)) T x := by
  obtain ⟨hd,hcu⟩ := contDiff_infty_iff_deriv.mp hu.1
  obtain ⟨hd',hcu'⟩ := contDiff_infty_iff_deriv.mp hcu
  have h1 := gaussianHeat_space_derivative hu.1.continuous.measurable hcu.continuous.measurable
    (row_terminal_quadratic_growth hu) (row_terminal_deriv_growth hu) (fun z => (hd z).hasDerivAt) T
  have h2 := gaussianHeat_space_derivative hcu.continuous.measurable hcu'.continuous.measurable
    (row_terminal_deriv_growth hu) (row_terminal_second_growth hu) (fun z => (hd' z).hasDerivAt) T
  have he : gaussianRowOperator 0 T u = gaussianHeat u T := by funext z; simp [gaussianRowOperator]
  rw [he,funext (fun z => (h1 z).deriv),(h2 x).deriv]

lemma gaussianRowOperator_curvature {u : ℝ → ℝ} {A B C κ Q a T : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hTQ : T ≤ Q) (x : ℝ) :
    -C ≤ deriv (deriv (gaussianRowOperator a T u)) x ∧
    deriv (deriv (gaussianRowOperator a T u)) x ≤ κ/(1-κ*T) := by
  have hk := hu.2.2.2.1
  have hkT : κ*T < 1 := (mul_le_mul_of_nonneg_left hTQ hk).trans_lt hu.2.2.2.2.1
  have hden : 0 < 1-κ*T := by linarith
  by_cases haz : a=0
  · subst a
    rw [gaussianRowOperator_second_zero hu T x]
    obtain ⟨_,hcu⟩ := contDiff_infty_iff_deriv.mp hu.1
    obtain ⟨_,hcu'⟩ := contDiff_infty_iff_deriv.mp hcu
    have hi := heat_affine_quadratic_integrable hcu'.continuous.measurable
      (row_terminal_second_growth hu) x (Real.sqrt T)
    have hl : -C ≤ gaussianHeat (deriv (deriv u)) T x := by
      calc
        -C = ∫ _ : ℝ,-C ∂gaussianReal 0 1 := by simp
        _ ≤ _ := integral_mono (integrable_const _) hi (fun z => (hu.2.2.2.2.2.2 _).2.2.1)
    have hr : gaussianHeat (deriv (deriv u)) T x ≤ κ := by
      calc
        _ ≤ ∫ _ : ℝ,κ ∂gaussianReal 0 1 :=
          integral_mono hi (integrable_const _) (fun z => (hu.2.2.2.2.2.2 _).2.2.2)
        _ = κ := by simp
    refine ⟨hl,hr.trans ?_⟩
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg hk hT.le]
  · let b := Real.sqrt T
    let w := fun z => Real.exp (a*u (x+b*z))
    have hb : 0 < b := Real.sqrt_pos.mpr hT
    have hb2 : b^2=T := Real.sq_sqrt hT.le
    have h := gaussianRowMoments hu ha x b
    have hZ : 0 < ∫ z,w z ∂gaussianReal 0 1 := integral_exp_pos h.zero
    have hJ : -C*(∫ z,w z ∂gaussianReal 0 1) ≤
        ∫ z,deriv (deriv u) (x+b*z)*w z ∂gaussianReal 0 1 := by
      rw [← integral_const_mul]
      exact integral_mono (h.zero.const_mul (-C)) h.curvature
        (fun z => mul_le_mul_of_nonneg_right (hu.2.2.2.2.2.2 _).2.2.1 (Real.exp_pos _).le)
    have hv := weighted_variance_nonneg (fun z => (Real.exp_pos (a*u (x+b*z))).le)
      h.zero h.slope h.slope_sq hZ
    have hc := weighted_covariance_upper (fun z => (Real.exp_pos (a*u (x+b*z))).le)
      (row_slope_antitone hu x hb.le) h.zero h.first h.second h.slope h.slope_first
    obtain ⟨hL,hK,hS⟩ := row_gaussian_stein hu ha x b
    have hD := gaussianRowOperator_second_moments hu ha haz T x
    have hh := row_curvature_algebra ha ha1 hb hk (by rwa [hb2]) hZ hJ hv hL hK hS hc hD
    simpa only [hb2] using hh

theorem gaussian_curvature : GaussianCurvatureStatement := by
  intro u A B C κ Q hQ hu a ha ha1 T hT hTQ x
  exact gaussianRowOperator_curvature hu ha ha1 hT hTQ x
end MicroscopicJamming

end

end OAI
