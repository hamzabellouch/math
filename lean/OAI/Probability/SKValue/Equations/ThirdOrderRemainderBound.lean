import Mathlib

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue

lemma third_order_remainder_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 3 f) (hK : 0≤K)
    (hbound : ∀ x, |iteratedDeriv 3 f x|≤K) (x d : ℝ) :
    |f (x+d)-f x-deriv f x*d-(1/2 : ℝ)*deriv (deriv f) x*d^2| ≤ K*|d|^3 := by
  by_cases hd : d=0
  · simp [hd]
  have hne : x ≠ x+d := by
    intro hx
    apply hd
    linarith
  have hu := uniqueDiffOn_uIcc hne
  have hmem : x ∈ uIcc x (x+d) := left_mem_uIcc
  have h1 : iteratedDerivWithin 1 f (uIcc x (x+d)) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hmem,
      iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 f (uIcc x (x+d)) x = deriv (deriv f) x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hmem,
      iteratedDeriv_succ, iteratedDeriv_one]
  have ht : taylorWithinEval f 2 (uIcc x (x+d)) x (x+d) =
      f x+deriv f x*d+(1/2 : ℝ)*deriv (deriv f) x*d^2 := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
    rw [h1, h2]
    norm_num
    ring
  obtain ⟨y,_,hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hne hf.contDiffOn
  rw [ht] at hy
  have heq : f (x+d)-f x-deriv f x*d-(1/2 : ℝ)*deriv (deriv f) x*d^2 =
      iteratedDeriv 3 f y*d^3/6 := by
    norm_num at hy
    linarith
  rw [heq, abs_div, abs_mul, abs_pow]
  norm_num
  have hh : |iteratedDeriv 3 f y| *|d|^3 ≤ K*|d|^3 :=
    mul_le_mul_of_nonneg_right (hbound y) (by positivity)
  have hp : 0≤K*|d|^3 := by positivity
  linarith

lemma gradient_generator_quadrature {γ : ℝ → ℝ} {b p : ℝ → ℝ → ℝ}
    {t δ x y G K L : ℝ} (hδ : 0 ≤ δ) (hG : 0 ≤ G) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0 ≤ γ t) (hγG : γ t ≤ G)
    (hp : ∀ s ∈ Icc t (t+δ), |p s y| ≤ K)
    (hbLip : ∀ s ∈ Icc t (t+δ), |b s y-b t x| ≤ L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), |p s y-p t x| ≤ L*(|s-t|+|y-x|))
    (hbint : IntervalIntegrable (fun s ↦ b s y) volume t (t+δ))
    (hpint : IntervalIntegrable (fun s ↦ γ s*p s y) volume t (t+δ)) :
    |(∫ s in t..(t+δ), (1/2 : ℝ)*b s y+γ s*p s y) -
        δ*((1/2 : ℝ)*b t x+γ t*p t x)| ≤
      δ*((1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t)) := by
  have het : t ∈ Icc t (t+δ) := ⟨le_rfl, by linarith⟩
  have heT : t+δ ∈ Icc t (t+δ) := ⟨by linarith, le_rfl⟩
  have hgap : 0 ≤ γ (t+δ)-γ t := sub_nonneg.mpr (hγ het heT (by linarith))
  have hpw : ∀ s ∈ Icc t (t+δ),
      |((1/2 : ℝ)*b s y+γ s*p s y)-((1/2 : ℝ)*b t x+γ t*p t x)| ≤
      (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t) := by
    intro s hs
    have hst := hγ het hs hs.1
    have hsT := hγ hs heT hs.2
    have hr : |s-t| ≤ δ := by rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    have hb' : |b s y-b t x| ≤ L*(δ+|y-x|) := (hbLip s hs).trans (by gcongr)
    have hp' : |p s y-p t x| ≤ L*(δ+|y-x|) := (hpLip s hs).trans (by gcongr)
    calc
      _ = |((1/2 : ℝ)*(b s y-b t x)+γ t*(p s y-p t x))+(γ s-γ t)*p s y| := by
        congr 1; ring
      _ ≤ |(1/2 : ℝ)*(b s y-b t x)|+|γ t*(p s y-p t x)|+|(γ s-γ t)*p s y| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = (1/2 : ℝ)*|b s y-b t x|+γ t*|p s y-p t x|+(γ s-γ t)*|p s y| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hγ0,
          abs_of_nonneg (sub_nonneg.mpr hst)]
        norm_num
      _ ≤ (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t) := by
        calc
          _ ≤ (1/2 : ℝ)*(L*(δ+|y-x|))+G*(L*(δ+|y-x|))+(γ (t+δ)-γ t)*K := by
            apply add_le_add
            · gcongr
            · calc
                _ ≤ (γ s-γ t)*K :=
                  mul_le_mul_of_nonneg_left (hp s hs) (sub_nonneg.mpr hst)
                _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_right hsT _) hK
          _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := t+δ)
    (f := fun s ↦ ((1/2 : ℝ)*b s y+γ s*p s y)-((1/2 : ℝ)*b t x+γ t*p t x))
    (C := (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t)) (fun s hs ↦ by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le (by linarith : t≤t+δ)] at hs
      exact hpw s ⟨hs.1.le, hs.2⟩)
  rw [intervalIntegral.integral_sub ((hbint.const_mul _).add hpint) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs,
    show t+δ-t=δ by ring, abs_of_nonneg hδ] at hi
  simpa only [mul_comm δ] using hi

lemma euler_cubic_remainder {δ G K C D c v a b vsp vend z : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤1) (hG : 0≤G) (hK : 0≤K) (hC : 0≤C)
    (hc : |c|≤G) (hv : |v|≤1) (hb : |b|≤K)
    (hsp : |vsp-v-a*(Real.sqrt δ*z+δ*c*v)-
      (1/2 : ℝ)*b*(Real.sqrt δ*z+δ*c*v)^2| ≤ K*|Real.sqrt δ*z+δ*c*v|^3)
    (htm : |vend-vsp+δ*((1/2 : ℝ)*b+c*v*a)| ≤
      δ*(C*(δ+|Real.sqrt δ*z+δ*c*v|)+K*D)) :
    |vend-v-a*Real.sqrt δ*z-(1/2 : ℝ)*δ*b*(z^2-1)| ≤
      δ*Real.sqrt δ*(K*(|z|+G)^3+C*(1+|z|+G)+K*G*(|z|+G/2))+δ*K*D := by
  let η := Real.sqrt δ
  let d := η*z+δ*c*v
  have hη : 0≤η := Real.sqrt_nonneg _
  have hηsq : η^2=δ := Real.sq_sqrt hδ
  have hη1 : η≤1 := (Real.sqrt_le_one).2 hδ1
  have hδη : δ≤η := by nlinarith
  have hcv : |c*v|≤G := by
    rw [abs_mul]
    calc |c| *|v| ≤ G*1 := mul_le_mul hc hv (abs_nonneg _) hG
         _ = G := mul_one _
  have hdcv : |δ*c*v|≤δ*G := by
    rw [mul_assoc δ, abs_mul, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left hcv hδ
  have hd : |d|≤η*(|z|+G) := by
    calc
      |d| ≤ |η*z|+|δ*c*v| := abs_add_le _ _
      _ ≤ η*|z|+δ*G := by rw [abs_mul, abs_of_nonneg hη]; gcongr
      _ ≤ η*(|z|+G) := by nlinarith
  have hcube : K*|d|^3 ≤ δ*η*(K*(|z|+G)^3) := by
    calc
      _ ≤ K*(η*(|z|+G))^3 := by gcongr
      _ = _ := by rw [← hηsq]; ring
  have htbound : δ*(C*(δ+|d|)+K*D) ≤ δ*η*(C*(1+|z|+G))+δ*K*D := by
    have hh : δ+|d| ≤ η*(1+|z|+G) := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hδ hC)
    nlinarith
  have hcross : |(1/2 : ℝ)*b*(d^2-δ*z^2)| ≤ δ*η*(K*G*(|z|+G/2)) := by
    have heq : d^2-δ*z^2 = (δ*c*v)*(2*η*z+δ*c*v) := by
      dsimp only [d]
      rw [← hηsq]
      ring
    have hsum : |2*η*z+δ*c*v| ≤ η*(2*|z|+G) := by
      calc
        _ ≤ |2*η*z|+|δ*c*v| := abs_add_le _ _
        _ ≤ 2*η*|z|+δ*G := by
          rw [abs_mul (2*η), abs_of_nonneg (by positivity : 0≤2*η)]
          gcongr
        _ ≤ η*(2*|z|+G) := by nlinarith
    rw [heq, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ)≤1/2)]
    calc
      _ ≤ (1/2 : ℝ)*K*((δ*G)*(η*(2*|z|+G))) := by gcongr
      _ = _ := by ring
  have heq : vend-v-a*η*z-(1/2 : ℝ)*δ*b*(z^2-1) =
      (vsp-v-a*d-(1/2 : ℝ)*b*d^2)+(vend-vsp+δ*((1/2 : ℝ)*b+c*v*a))+
        (1/2 : ℝ)*b*(d^2-δ*z^2) := by dsimp only [d]; ring
  change |vend-v-a*η*z-(1/2 : ℝ)*δ*b*(z^2-1)| ≤ _
  rw [heq]
  calc
    _ ≤ |vsp-v-a*d-(1/2 : ℝ)*b*d^2|+|vend-vsp+δ*((1/2 : ℝ)*b+c*v*a)|+
        |(1/2 : ℝ)*b*(d^2-δ*z^2)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K*|d|^3+δ*(C*(δ+|d|)+K*D)+δ*η*(K*G*(|z|+G/2)) := by gcongr
    _ ≤ δ*η*(K*(|z|+G)^3+C*(1+|z|+G)+K*G*(|z|+G/2))+δ*K*D := by linarith

lemma gradient_euler_one_step {u : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {t δ x z G K L : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hG : 0≤G) (hK : 0≤K) (hL : 0≤L)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0≤γ t) (hγG : γ t≤G)
    (hu : |u t x|≤1) (hsmooth : ContDiff ℝ 3 (u t))
    (hb : |deriv (deriv (u t)) x|≤K) (hthird : ∀ y, |iteratedDeriv 3 (u t) y|≤K)
    (hp : ∀ s ∈ Icc t (t+δ), ∀ y, |u s y*deriv (u s) y|≤K)
    (hbLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |deriv (deriv (u s)) y-deriv (deriv (u t)) x|≤L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |u s y*deriv (u s) y-u t x*deriv (u t) x|≤L*(|s-t|+|y-x|))
    (hbint : ∀ y, IntervalIntegrable (fun s ↦ deriv (deriv (u s)) y) volume t (t+δ))
    (hpint : ∀ y, IntervalIntegrable (fun s ↦ γ s*(u s y*deriv (u s) y)) volume t (t+δ))
    (hPDE : ∀ y, u (t+δ) y-u t y =
      -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (u s)) y+γ s*(u s y*deriv (u s) y))) :
    let d := Real.sqrt δ*z+δ*γ t*u t x
    |u (t+δ) (x+d)-u t x-deriv (u t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (u t)) x*(z^2-1)| ≤
    δ*Real.sqrt δ*(K*(|z|+G)^3+(1/2+G)*L*(1+|z|+G)+K*G*(|z|+G/2))+
      δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*γ t*u t x
  have htm := gradient_generator_quadrature (b := fun s y ↦ deriv (deriv (u s)) y)
    (p := fun s y ↦ u s y*deriv (u s) y) (y := x+d) hδ hG hK hL hγ hγ0 hγG
    (fun s hs ↦ hp s hs _) (fun s hs ↦ hbLip s hs _) (fun s hs ↦ hpLip s hs _)
    (hbint _) (hpint _)
  have ht : |u (t+δ) (x+d)-u t (x+d)+
      δ*((1/2 : ℝ)*deriv (deriv (u t)) x+γ t*u t x*deriv (u t) x)| ≤
      δ*(((1/2 : ℝ)+G)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    rw [hPDE]
    have heq : -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (u s)) (x+d)+
        γ s*(u s (x+d)*deriv (u s) (x+d)))+
        δ*((1/2 : ℝ)*deriv (deriv (u t)) x+γ t*u t x*deriv (u t) x) =
      -((∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (u s)) (x+d)+
        γ s*(u s (x+d)*deriv (u s) (x+d)))-
        δ*((1/2 : ℝ)*deriv (deriv (u t)) x+γ t*(u t x*deriv (u t) x))) := by ring
    rw [heq, abs_neg]
    simpa only [add_sub_cancel_left] using htm
  exact euler_cubic_remainder hδ hδ1 hG hK (by positivity)
    (by rwa [abs_of_nonneg hγ0]) hu hb (third_order_remainder_bound hsmooth hK hthird x d) ht

end SKValue

end

end OAI
