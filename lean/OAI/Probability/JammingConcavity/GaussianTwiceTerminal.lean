import Mathlib
import OAI.Probability.JammingConcavity.LogHeatCalculus

namespace OAI

/-! Gaussian Twice Terminal. -/

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
namespace Twice

 

structure RowTwiceTerminal (u : ℝ → ℝ) (A B C κ Q : ℝ) : Prop where
  differentiable : Differentiable ℝ u
  deriv_differentiable : Differentiable ℝ (deriv u)
  A_nonneg : 0 ≤ A
  C_nonneg : 0 ≤ C
  kappa_nonneg : 0 ≤ κ
  subcritical : κ*Q < 1
  bounds : ∀ x, -A*(1+x^2) ≤ u x ∧ u x ≤ B ∧
    -C ≤ deriv (deriv u) x ∧ deriv (deriv u) x ≤ κ

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

lemma row_terminal_deriv_linear {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x, |deriv u x| ≤ L*(1+|x|) := by
  have hdu := hu.differentiable
  have hdu' := hu.deriv_differentiable
  let L := |deriv u 0|+C+κ
  refine ⟨L, by dsimp [L]; linarith [abs_nonneg (deriv u 0),hu.C_nonneg,hu.kappa_nonneg], ?_⟩
  intro x
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := deriv u) (s := univ) (C := C+κ) (fun y _ => hdu' y)
    (fun y _ => by
      rw [Real.norm_eq_abs, abs_le]
      have hy := hu.bounds y
      constructor <;> linarith [hy.2.2.1,hy.2.2.2,hu.C_nonneg,hu.kappa_nonneg])
    (convex_univ) (x := 0) (y := x) (mem_univ _) (mem_univ _)
  simp only [Real.norm_eq_abs, sub_zero] at hh
  have ha := abs_add_le (deriv u x-deriv u 0) (deriv u 0)
  rw [sub_add_cancel] at ha
  dsimp [L]
  nlinarith [hu.C_nonneg, hu.kappa_nonneg, abs_nonneg (deriv u 0), abs_nonneg x, mul_nonneg (abs_nonneg (deriv u 0)) (abs_nonneg x)]

lemma row_terminal_quadratic_growth {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) : HeatQuadraticGrowth u := by
  refine ⟨A+|B|, by linarith [hu.A_nonneg,abs_nonneg B], ?_⟩
  intro x
  have hb := hu.bounds x
  have hsq : x^2 ≤ (1+|x|)^2 := by nlinarith [sq_abs x, abs_nonneg x]
  rw [abs_le]
  constructor
  · nlinarith [hu.A_nonneg,abs_nonneg B, mul_nonneg (abs_nonneg B) (sq_nonneg (1+|x|)),sq_abs x,abs_nonneg x]
  · have hp : 1 ≤ (1+|x|)^2 := by nlinarith [abs_nonneg x,sq_nonneg x,sq_abs x]
    have h := mul_le_mul_of_nonneg_left hp (abs_nonneg B)
    nlinarith [le_abs_self B,hu.A_nonneg,mul_nonneg hu.A_nonneg (sq_nonneg (1+|x|))]

lemma row_terminal_deriv_growth {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) : HeatQuadraticGrowth (deriv u) := by
  obtain ⟨L,hL,h⟩ := row_terminal_deriv_linear hu
  refine ⟨L,hL,fun x => (h x).trans (mul_le_mul_of_nonneg_left ?_ hL)⟩
  nlinarith [abs_nonneg x, sq_nonneg x,sq_abs x]

lemma row_terminal_second_growth {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) : HeatQuadraticGrowth (deriv (deriv u)) := by
  have hK : 0 ≤ C+κ := add_nonneg hu.C_nonneg hu.kappa_nonneg
  refine ⟨C+κ,hK,fun x => ?_⟩
  have h : |deriv (deriv u) x| ≤ C+κ := by
    rw [abs_le]; have hx := hu.bounds x
    constructor <;> linarith [hx.2.2.1,hx.2.2.2,hu.C_nonneg,hu.kappa_nonneg]
  exact h.trans (le_mul_of_one_le_right hK (by nlinarith [abs_nonneg x,sq_nonneg x,sq_abs x]))

 
lemma row_exp_derivatives {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) (a : ℝ) :
    (∀ x, HasDerivAt (fun y => Real.exp (a*u y)) (rowExpFirst a u x) x) ∧
    (∀ x, HasDerivAt (rowExpFirst a u) (rowExpSecond a u x) x) := by
  have hdu := hu.differentiable
  have hdu' := hu.deriv_differentiable
  constructor
  · intro x
    convert ((hdu x).hasDerivAt.const_mul a).exp using 1
    first | rfl | (simp only [rowExpFirst]; ring)
  · intro x
    convert (((hdu' x).hasDerivAt.const_mul a).mul
      ((hdu x).hasDerivAt.const_mul a).exp) using 1 <;> first | rfl | (dsimp only [rowExpFirst,rowExpSecond]; ring)

lemma row_exp_measurable {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) (a : ℝ) :
    Measurable (fun x => Real.exp (a*u x)) ∧ Measurable (rowExpFirst a u) ∧
      Measurable (rowExpSecond a u) := by
  have h0 := hu.differentiable.continuous.measurable
  have h1 := hu.deriv_differentiable.continuous.measurable
  have h2 := measurable_deriv (f := deriv u)
  refine ⟨?_, ?_, ?_⟩
  · fun_prop
  · unfold rowExpFirst; fun_prop
  · unfold rowExpSecond; fun_prop

lemma row_exp_growth {u : ℝ → ℝ} {A B C κ Q a : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) :
    HeatQuadraticGrowth (fun x => Real.exp (a*u x)) ∧
    HeatQuadraticGrowth (rowExpFirst a u) ∧ HeatQuadraticGrowth (rowExpSecond a u) := by
  obtain ⟨L,hL,hlin⟩ := row_terminal_deriv_linear hu
  have hD : 0 ≤ C+κ := add_nonneg hu.C_nonneg hu.kappa_nonneg
  have he (x : ℝ) : Real.exp (a*u x) ≤ Real.exp (a*B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hu.bounds x).2.1 ha)
  have hs (x : ℝ) : 1 ≤ (1+|x|)^2 := by nlinarith [abs_nonneg x,sq_nonneg x,sq_abs x]
  have hd (x : ℝ) : |deriv (deriv u) x| ≤ C+κ := by
    rw [abs_le]
    have hh := hu.bounds x
    constructor <;> linarith [hh.2.2.1,hh.2.2.2,hu.C_nonneg,hu.kappa_nonneg]
  constructor
  · refine ⟨Real.exp (a*B),(Real.exp_pos _).le,fun x => ?_⟩
    rw [abs_of_pos (Real.exp_pos _)]
    exact (he x).trans (le_mul_of_one_le_right (Real.exp_pos _).le (hs x))
  constructor
  · refine ⟨a*L*Real.exp (a*B),by positivity,fun x => ?_⟩
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left (hlin x) ha) (he x)
      (Real.exp_pos _).le (by positivity : 0 ≤ a*(L*(1+|x|)))
    dsimp [rowExpFirst]
    rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (a*(L*(1+|x|)))*Real.exp (a*B) := hh
      _ ≤ a*L*Real.exp (a*B)*(1+|x|)^2 := by
        have hh := mul_le_mul_of_nonneg_left
          (show 1+|x| ≤ (1+|x|)^2 by nlinarith [abs_nonneg x,sq_nonneg x,sq_abs x])
          (show 0 ≤ a*L*Real.exp (a*B) by positivity)
        nlinarith
  · refine ⟨(a*(C+κ)+a^2*L^2)*Real.exp (a*B),by positivity,fun x => ?_⟩
    have hp : (deriv u x)^2 ≤ (L*(1+|x|))^2 := by
      nlinarith [sq_le_sq₀ (abs_nonneg (deriv u x)) (show 0 ≤ L*(1+|x|) by positivity) |>.mpr (hlin x), sq_abs (deriv u x)]
    have hq : |a*deriv (deriv u) x+a^2*(deriv u x)^2| ≤
        (a*(C+κ)+a^2*L^2)*(1+|x|)^2 := by
      calc
        _ ≤ |a*deriv (deriv u) x|+|a^2*(deriv u x)^2| := abs_add_le _ _
        _ = a*|deriv (deriv u) x|+a^2*(deriv u x)^2 := by
          rw [abs_mul, abs_of_nonneg ha, abs_of_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg _))]
        _ ≤ a*(C+κ)+a^2*(L*(1+|x|))^2 := add_le_add
          (mul_le_mul_of_nonneg_left (hd x) ha) (mul_le_mul_of_nonneg_left hp (sq_nonneg a))
        _ ≤ (a*(C+κ)+a^2*L^2)*(1+|x|)^2 := by
          have hh := mul_le_mul_of_nonneg_left (hs x) (show 0 ≤ a*(C+κ) by positivity)
          nlinarith
    dsimp [rowExpSecond]
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ ((a*(C+κ)+a^2*L^2)*(1+|x|)^2)*Real.exp (a*B) :=
        mul_le_mul hq (he x) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring

 
lemma gaussianRowOperator_calculus {u : ℝ → ℝ} {A B C κ Q a T : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (hT : 0 < T) :
    Differentiable ℝ (gaussianRowOperator a T u) ∧
    Differentiable ℝ (deriv (gaussianRowOperator a T u)) ∧
    ∀ x, HasDerivAt (fun r => gaussianRowOperator a r u x)
      ((1/2:ℝ)*(deriv (deriv (gaussianRowOperator a T u)) x+
        a*(deriv (gaussianRowOperator a T u) x)^2)) T := by
  by_cases haz : a=0
  · subst a
    have hd := hu.differentiable
    have hd' := hu.deriv_differentiable
    have hh := gaussianHeat_twice_calculus hu.differentiable.continuous.measurable
      hu.deriv_differentiable.continuous.measurable (measurable_deriv (f := deriv u))
      (row_terminal_quadratic_growth hu) (row_terminal_deriv_growth hu)
      (row_terminal_second_growth hu) (fun x => (hd x).hasDerivAt)
      (fun x => (hd' x).hasDerivAt) hT
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

 
structure GaussianRowMoments (u : ℝ → ℝ) (a x b : ℝ) : Prop where
  zero : Integrable (fun z => Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  first : Integrable (fun z => z*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  second : Integrable (fun z => z^2*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  slope : Integrable (fun z => deriv u (x+b*z)*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  slope_first : Integrable (fun z => z*deriv u (x+b*z)*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  slope_sq : Integrable (fun z => (deriv u (x+b*z))^2*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)
  curvature : Integrable (fun z => deriv (deriv u) (x+b*z)*Real.exp (a*u (x+b*z))) (gaussianReal 0 1)

lemma gaussianRowMoments {u : ℝ → ℝ} {A B C κ Q a : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (x b : ℝ) : GaussianRowMoments u a x b := by
  obtain ⟨L,hL,hlin⟩ := row_terminal_deriv_linear hu
  let K := L*(1+|x|+|b|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound (z : ℝ) : |deriv u (x+b*z)| ≤ K*(1+|z|) := by
    exact (hlin _).trans (by dsimp [K]; nlinarith [mul_le_mul_of_nonneg_left (heat_affine_bound x b z) hL])
  have hb (z : ℝ) : |deriv (deriv u) (x+b*z)| ≤ C+κ := by
    rw [abs_le]; have hh := hu.bounds (x+b*z)
    constructor <;> linarith [hh.2.2.1,hh.2.2.2,hu.C_nonneg,hu.kappa_nonneg]
  have h0 := hu.differentiable.continuous.measurable
  have h1 := hu.deriv_differentiable.continuous.measurable
  have h2 := measurable_deriv (f := deriv u)
  have hw : Measurable (fun z => Real.exp (a*u (x+b*z))) := by fun_prop
  have hwM (z : ℝ) : |Real.exp (a*u (x+b*z))| ≤ Real.exp (a*B) := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hu.bounds _).2.1 ha)
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
  · exact hi (by fun_prop) (add_nonneg hu.C_nonneg hu.kappa_nonneg) 0 (fun z => by simpa using hb z)

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

lemma row_gaussian_stein {u : ℝ → ℝ} {A B C κ Q a : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (x b : ℝ) :
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
  have hdu := hu.differentiable
  have hdu' := hu.deriv_differentiable
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

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

lemma gaussianRowOperator_second_exp {u : ℝ → ℝ} {A B C κ Q a : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (haz : a ≠ 0) (T x : ℝ) :
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
    (hu : RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (haz : a ≠ 0) (T x : ℝ) :
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

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

lemma row_slope_antitone {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) (x : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    Antitone (fun z => deriv u (x+b*z)-(κ*b)*z) := by
  have hd := hu.deriv_differentiable
  have hh (z : ℝ) : HasDerivAt (fun r => deriv u (x+b*r)-(κ*b)*r)
      (deriv (deriv u) (x+b*z)*b-κ*b) z := by
    have hy : HasDerivAt (fun r : ℝ => x+b*r) b z := by
      convert (hasDerivAt_const z x).add ((hasDerivAt_id z).const_mul b) using 1 <;> first | rfl | simp
    convert ((hd _).hasDerivAt.comp z hy).sub ((hasDerivAt_id z).const_mul (κ*b)) using 1 <;> first | rfl | simp
  apply antitone_of_deriv_nonpos (fun z => (hh z).differentiableAt)
  intro z
  rw [(hh z).deriv]
  exact sub_nonpos.mpr (mul_le_mul_of_nonneg_right (hu.bounds _).2.2.2 hb)

lemma gaussianRowOperator_second_zero {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) (T x : ℝ) :
    deriv (deriv (gaussianRowOperator 0 T u)) x = gaussianHeat (deriv (deriv u)) T x := by
  have hd := hu.differentiable
  have hd' := hu.deriv_differentiable
  have h1 := gaussianHeat_space_derivative hu.differentiable.continuous.measurable hu.deriv_differentiable.continuous.measurable
    (row_terminal_quadratic_growth hu) (row_terminal_deriv_growth hu) (fun z => (hd z).hasDerivAt) T
  have h2 := gaussianHeat_space_derivative hu.deriv_differentiable.continuous.measurable (measurable_deriv (f := deriv u))
    (row_terminal_deriv_growth hu) (row_terminal_second_growth hu) (fun z => (hd' z).hasDerivAt) T
  have he : gaussianRowOperator 0 T u = gaussianHeat u T := by funext z; simp [gaussianRowOperator]
  rw [he,funext (fun z => (h1 z).deriv),(h2 x).deriv]

lemma gaussianRowOperator_curvature {u : ℝ → ℝ} {A B C κ Q a T : ℝ}
    (hu : RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hTQ : T ≤ Q) (x : ℝ) :
    -C ≤ deriv (deriv (gaussianRowOperator a T u)) x ∧
    deriv (deriv (gaussianRowOperator a T u)) x ≤ κ/(1-κ*T) := by
  have hk := hu.kappa_nonneg
  have hkT : κ*T < 1 := (mul_le_mul_of_nonneg_left hTQ hk).trans_lt hu.subcritical
  have hden : 0 < 1-κ*T := by linarith
  by_cases haz : a=0
  · subst a
    rw [gaussianRowOperator_second_zero hu T x]
    
    have hi := heat_affine_quadratic_integrable (measurable_deriv (f := deriv u))
      (row_terminal_second_growth hu) x (Real.sqrt T)
    have hl : -C ≤ gaussianHeat (deriv (deriv u)) T x := by
      calc
        -C = ∫ _ : ℝ,-C ∂gaussianReal 0 1 := by simp
        _ ≤ _ := integral_mono (integrable_const _) hi (fun z => (hu.bounds _).2.2.1)
    have hr : gaussianHeat (deriv (deriv u)) T x ≤ κ := by
      calc
        _ ≤ ∫ _ : ℝ,κ ∂gaussianReal 0 1 :=
          integral_mono hi (integrable_const _) (fun z => (hu.bounds _).2.2.2)
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
        (fun z => mul_le_mul_of_nonneg_right (hu.bounds _).2.2.1 (Real.exp_pos _).le)
    have hv := weighted_variance_nonneg (fun z => (Real.exp_pos (a*u (x+b*z))).le)
      h.zero h.slope h.slope_sq hZ
    have hc := weighted_covariance_upper (fun z => (Real.exp_pos (a*u (x+b*z))).le)
      (row_slope_antitone hu x hb.le) h.zero h.first h.second h.slope h.slope_first
    obtain ⟨hL,hK,hS⟩ := row_gaussian_stein hu ha x b
    have hD := gaussianRowOperator_second_moments hu ha haz T x
    have hh := row_curvature_algebra ha ha1 hb hk (by rwa [hb2]) hZ hJ hv hL hK hS hc hD
    simpa only [hb2] using hh

end Twice
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma gaussianHeat_eq_variance_integral {v : ℝ → ℝ} (hv : Measurable v)
    {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    gaussianHeat v T x = ∫ z,v (x+z) ∂gaussianReal 0 (⟨T,hT⟩ : ℝ≥0) := by
  have he : (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt T*z) = gaussianReal 0 ⟨T,hT⟩ := by
    rw [gaussianReal_map_const_mul,mul_zero,mul_one]
    congr 1
    exact Subtype.ext (Real.sq_sqrt hT)
  rw [← he]
  symm
  exact integral_map (by fun_prop) ((show Measurable (fun z : ℝ => v (x+z)) from hv.comp (by fun_prop)).aestronglyMeasurable)

lemma gaussianRowOperator_barrier {u : ℝ → ℝ} (hu : Measurable u)
    {A B R a T : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hb : ∀ z,-A*(1+z^2+R) ≤ u z ∧ u z ≤ B) (x : ℝ) :
    -A*(1+x^2+R+T) ≤ gaussianRowOperator a T u x ∧ gaussianRowOperator a T u x ≤ B := by
  have : IsProbabilityMeasure (gaussianReal 0 (⟨T,hT⟩ : ℝ≥0)) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  by_cases haz : a=0
  · simp only [gaussianRowOperator,ite_eq_left haz]
    rw [gaussianHeat_eq_variance_integral hu hT]
    refine ⟨gaussian_envelope_integral_lower hu hA hR hb x ⟨T,hT⟩,?_⟩
    calc
      _ ≤ ∫ _ : ℝ,B ∂gaussianReal 0 (⟨T,hT⟩ : ℝ≥0) :=
        integral_mono (gaussian_envelope_integrable hu hA hR hb x ⟨T,hT⟩)
          (integrable_const _) (fun z => (hb _).2)
      _ = B := by simp
  · simp only [gaussianRowOperator,ite_eq_right haz]
    rw [gaussianHeat_eq_variance_integral ((hu.const_mul a).exp) hT]
    exact (gaussian_log_operator_barrier hu hA hR hb (lt_of_le_of_ne ha (Ne.symm haz)) x ⟨T,hT⟩).2

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma gaussianStepTime_nonneg {rs : List (ℝ × ℝ)}
    (hs : ∀ r ∈ rs, 0 ≤ r.2) : 0 ≤ gaussianStepTime rs := by
  unfold gaussianStepTime
  apply List.sum_nonneg
  intro x hx
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
  exact hs r hr

lemma gaussian_curvature_update {κ R T : ℝ} (hκ : 0 ≤ κ) (_hR : 0 ≤ R) (hT : 0 ≤ T)
    (h : κ*(T+R)<1) :
    0 ≤ κ/(1-κ*R) ∧ κ/(1-κ*R)*T<1 ∧
    (κ/(1-κ*R))/(1-(κ/(1-κ*R))*T)=κ/(1-κ*(T+R)) := by
  have hKR : κ*R<1 := by nlinarith [mul_nonneg hκ hT]
  have hp : 0 < 1-κ*R := by linarith
  have hpt : 0 < 1-κ*(T+R) := by linarith
  have hv : κ/(1-κ*R)*T<1 := by
    rw [div_mul_eq_mul_div,div_lt_one hp]
    nlinarith
  refine ⟨div_nonneg hκ hp.le,hv,?_⟩
  have hpv : 0 < 1-(κ/(1-κ*R))*T := by linarith
  have he : 1-(κ/(1-κ*R))*T=(1-κ*(T+R))/(1-κ*R) := by
    field_simp [hp.ne']
    ring
  rw [he]
  field_simp [hp.ne',hpt.ne']

theorem gaussian_step_bounds : GaussianStepBoundsStatement := by
  intro u A B C κ Q hQ hu rs
  induction rs with
  | nil =>
    intro _ _
    obtain ⟨hd,hcu⟩ := contDiff_infty_iff_deriv.mp hu.1
    have hd' := (contDiff_infty_iff_deriv.mp hcu).1
    refine ⟨hd,hd',fun x => ?_⟩
    have hx := hu.2.2.2.2.2.2 x
    simpa [gaussianRowComposition,gaussianStepTime] using And.intro (And.intro hx.1 hx.2.1) hx.2.2
  | cons r rs ih =>
    intro hrs hsum
    have hr := hrs r (by simp)
    have htail : ∀ t ∈ rs, 0 ≤ t.1 ∧ t.1 ≤ 1 ∧ 0 ≤ t.2 := fun t ht => hrs t (by simp [ht])
    have hR : 0 ≤ gaussianStepTime rs := gaussianStepTime_nonneg (fun t ht => (htail t ht).2.2)
    have htime : gaussianStepTime (r::rs)=r.2+gaussianStepTime rs := by simp [gaussianStepTime]
    rw [htime] at hsum
    obtain ⟨hd,hd',hb⟩ := ih htail (by linarith)
    have hk := hu.2.2.2.1
    have hKtot : κ*(r.2+gaussianStepTime rs)<1 :=
      (mul_le_mul_of_nonneg_left hsum hk).trans_lt hu.2.2.2.2.1
    obtain ⟨hkn,hsub,hupdate⟩ := gaussian_curvature_update hk hR hr.2.2 hKtot
    have he : gaussianRowComposition (r::rs) u =
      gaussianRowOperator r.1 r.2 (gaussianRowComposition rs u) := by rfl
    have htw : Twice.RowTwiceTerminal (gaussianRowComposition rs u)
        (A*(1+gaussianStepTime rs)) B C (κ/(1-κ*gaussianStepTime rs)) r.2 := by
      refine ⟨hd,hd',mul_nonneg hu.2.1 (by linarith),hu.2.2.1,hkn,hsub,fun z => ?_⟩
      refine ⟨?_,(hb z).1.2,(hb z).2⟩
      have hf := (hb z).1.1
      have hh := mul_nonneg (mul_nonneg hu.2.1 hR) (sq_nonneg z)
      nlinarith
    have hbar (x : ℝ) : -A*(1+x^2+gaussianStepTime (r::rs)) ≤
        gaussianRowComposition (r::rs) u x ∧ gaussianRowComposition (r::rs) u x ≤ B := by
      rw [he,htime]
      have hh := gaussianRowOperator_barrier hd.continuous.measurable hu.2.1 hR hr.1 hr.2.2
        (fun z => (hb z).1) x
      convert hh using 1
      ring_nf
    by_cases hzero : r.2=0
    · have hz : gaussianRowComposition (r::rs) u = gaussianRowComposition rs u := by
        rw [he,hzero]; funext x; exact gaussianRowOperator_zero _ _ _
      refine ⟨hz.symm ▸ hd,hz.symm ▸ hd',fun x => ⟨hbar x,?_⟩⟩
      simpa only [hz,htime,hzero,zero_add] using (hb x).2
    · have hpos : 0 < r.2 := lt_of_le_of_ne hr.2.2 (Ne.symm hzero)
      obtain ⟨hf,hf',_⟩ := Twice.gaussianRowOperator_calculus htw hr.1 hpos
      refine ⟨he.symm ▸ hf,he.symm ▸ hf',fun x => ⟨hbar x,?_⟩⟩
      have hc := Twice.gaussianRowOperator_curvature htw hr.1 hr.2.1 hpos le_rfl x
      rw [hupdate] at hc
      simpa only [he,htime] using hc
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma gaussianStepRemainder_valid {rs : List (ℝ × ℝ)}
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) {t : ℝ} (ht : 0 ≤ t) :
    (∀ r ∈ gaussianStepRemainder rs t, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) ∧
    gaussianStepTime (gaussianStepRemainder rs t) = max (gaussianStepTime rs-t) 0 := by
  induction rs generalizing t with
  | nil =>
    constructor
    · simp [gaussianStepRemainder]
    · simp [gaussianStepRemainder,gaussianStepTime,max_eq_right (by linarith : -t ≤ 0)]
  | cons r rs ih =>
    have hr := hrs r (by simp)
    have htail : ∀ v ∈ rs, 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2 := fun v hv => hrs v (by simp [hv])
    have hR := gaussianStepTime_nonneg (fun v hv => (htail v hv).2.2)
    have hsum : gaussianStepTime (r::rs)=r.2+gaussianStepTime rs := by simp [gaussianStepTime]
    by_cases htr : t ≤ r.2
    · simp only [gaussianStepRemainder,ite_eq_left htr]
      constructor
      · intro v hv
        rcases List.mem_cons.mp hv with h | h
        · subst v; exact ⟨hr.1,hr.2.1,sub_nonneg.mpr htr⟩
        · exact htail v h
      · rw [hsum,max_eq_left (by linarith)]
        simp only [gaussianStepTime,List.map_cons,List.sum_cons]
        ring
    · have ht' : 0 ≤ t-r.2 := by linarith
      obtain ⟨hv,hvT⟩ := ih htail ht'
      simp only [gaussianStepRemainder,ite_eq_right htr]
      refine ⟨hv,?_⟩
      rw [hvT,hsum]
      congr 1
      ring

lemma gaussianStepRemainder_zero {rs : List (ℝ × ℝ)}
    (hrs : ∀ r ∈ rs, 0 ≤ r.2) : gaussianStepRemainder rs 0 = rs := by
  cases rs with
  | nil => rfl
  | cons r rs => simp [gaussianStepRemainder,hrs r (by simp)]

lemma gaussianRowComposition_zero_time {rs : List (ℝ × ℝ)}
    (hrs : ∀ r ∈ rs, 0 ≤ r.2) (hT : gaussianStepTime rs=0) (u : ℝ → ℝ) :
    gaussianRowComposition rs u=u := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := hrs r (by simp)
    have htail : ∀ v ∈ rs, 0 ≤ v.2 := fun v hv => hrs v (by simp [hv])
    have hR := gaussianStepTime_nonneg htail
    have hsum : gaussianStepTime (r::rs)=r.2+gaussianStepTime rs := by simp [gaussianStepTime]
    have hz : r.2=0 := by linarith
    have hzR : gaussianStepTime rs=0 := by linarith
    have he := ih htail hzR
    funext x
    change gaussianRowOperator r.1 r.2 (gaussianRowComposition rs u) x = u x
    rw [hz,he]
    exact gaussianRowOperator_zero _ _ _

lemma gaussianStepPath_zero {rs : List (ℝ × ℝ)}
    (hrs : ∀ r ∈ rs, 0 ≤ r.2) (u : ℝ → ℝ) :
    gaussianStepPath rs u 0=gaussianRowComposition rs u := by
  funext x
  simp [gaussianStepPath,gaussianStepRemainder_zero hrs]

lemma gaussianStepPath_terminal {rs : List (ℝ × ℝ)}
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) (u : ℝ → ℝ) :
    gaussianStepPath rs u (gaussianStepTime rs)=u := by
  have hR := gaussianStepTime_nonneg (fun r hr => (hrs r hr).2.2)
  obtain ⟨hv,hvT⟩ := gaussianStepRemainder_valid hrs hR
  have hz : gaussianStepTime (gaussianStepRemainder rs (gaussianStepTime rs))=0 := by simpa using hvT
  exact gaussianRowComposition_zero_time (fun r hr => (hv r hr).2.2) hz u

lemma gaussianStepPath_cons_le (r : ℝ × ℝ) (rs : List (ℝ × ℝ)) (u : ℝ → ℝ)
    {t : ℝ} (ht : t ≤ r.2) :
    gaussianStepPath (r::rs) u t=gaussianRowOperator r.1 (r.2-t) (gaussianRowComposition rs u) := by
  funext x
  simp [gaussianStepPath,gaussianStepRemainder,ht,gaussianRowComposition]

lemma gaussianStepPath_cons_gt (r : ℝ × ℝ) (rs : List (ℝ × ℝ)) (u : ℝ → ℝ)
    {t : ℝ} (ht : r.2 < t) :
    gaussianStepPath (r::rs) u t=gaussianStepPath rs u (t-r.2) := by
  funext x
  simp [gaussianStepPath,gaussianStepRemainder,not_le.mpr ht]
end MicroscopicJamming

 
 

namespace MicroscopicJamming

def GaussianStepTimeStatement : Prop :=
  ∀ A B C κ Q : ℝ, 0 < Q → 0 ≤ A → 0 ≤ C → 0 ≤ κ → κ*Q < 1 →
  ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℝ → ℝ, RowAnalyticTerminal u A B C κ Q →
  ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
  ∀ a s t : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ s → 0 ≤ t →
    max s t + gaussianStepTime rs ≤ Q → ∀ x,
    |gaussianRowOperator a t (gaussianRowComposition rs u) x -
      gaussianRowOperator a s (gaussianRowComposition rs u) x| ≤
      D*(1+x^2)*|t-s|
end MicroscopicJamming

 
 

namespace MicroscopicJamming

def GaussianStepSlopeStatement : Prop :=
  ∀ A B C κ Q : ℝ, 0 < Q → 0 ≤ A → 0 ≤ C → 0 ≤ κ → κ*Q < 1 →
  ∃ L : ℝ, 0 ≤ L ∧ ∀ u : ℝ → ℝ, RowAnalyticTerminal u A B C κ Q →
  ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    gaussianStepTime rs ≤ Q →
    ∀ x, |deriv (gaussianRowComposition rs u) x| ≤ L*(1+|x|)
end MicroscopicJamming

end

end OAI
