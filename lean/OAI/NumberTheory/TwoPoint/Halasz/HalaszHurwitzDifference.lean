import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons

namespace OAI

/-! Uniform control of the difference between a shifted and unshifted
Dirichlet term. This removes the singular first Hurwitz term before
continuation into the half-plane with positive real part. -/
namespace TwoPointCorrelations

open Complex Filter MeasureTheory
open scoped Topology

noncomputable def halaszHurwitzDifference (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((n+1:ℕ):ℝ)+a:ℂ)^(-s)-((n+1:ℕ):ℂ)^(-s)

lemma halasz_shifted_cpow_difference {x a : ℝ} (hx : 0<x) (ha : 0≤a)
    {s : ℂ} (hs : 0<s.re) :
    ‖((x+a:ℝ):ℂ)^(-s)-(x:ℂ)^(-s)‖≤‖s‖*x^(-(s.re+1))*a := by
  have hs0 : -s≠0 := neg_ne_zero.mpr (fun h => by subst s; simp at hs)
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun y : ℝ => (y:ℂ)^(-s))
    (f' := fun y => -s*(y:ℂ)^(-s-1)) (a := x) (b := x+a)
    (C := ‖s‖*x^(-(s.re+1)))
    (fun y hy => (hasDerivAt_ofReal_cpow_const (by linarith [hy.1]) hs0).hasDerivWithinAt)
    (fun y hy => by
      rw [norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hy.1])]
      simp only [Complex.sub_re,Complex.neg_re,Complex.one_re]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
      rw [show -s.re-1= -(s.re+1) by ring]
      exact Real.rpow_le_rpow_of_nonpos hx hy.1 (by linarith))
    (x+a) (by constructor <;> linarith)
  simpa only [add_sub_cancel_left] using hh

lemma halasz_hurwitz_difference_norm {a : ℝ} (ha : a∈Set.Icc (0:ℝ) 1)
    (n : ℕ) {s : ℂ} (hs : 0<s.re) :
    ‖halaszHurwitzDifference a n s‖≤‖s‖*((n+1:ℕ):ℝ)^(-(s.re+1)) := by
  have hh := halasz_shifted_cpow_difference
    (x := ((n+1:ℕ):ℝ)) (by positivity) ha.1 hs
  have hpos : 0≤‖s‖*((n+1:ℕ):ℝ)^(-(s.re+1)) := by positivity
  have hh' := hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha.2 hpos)
  simpa only [halaszHurwitzDifference,Complex.ofReal_add,Complex.ofReal_natCast] using hh'

lemma halasz_hurwitz_difference_summable {a : ℝ} (ha : a∈Set.Icc (0:ℝ) 1)
    {s : ℂ} (hs : 0<s.re) : Summable (fun n => halaszHurwitzDifference a n s) := by
  have hp : Summable (fun n : ℕ => ((n+1:ℕ):ℝ)^(-(s.re+1))) :=
    (Real.summable_nat_rpow.mpr (by linarith)).comp_injective Nat.succ_injective
  exact (hp.mul_left ‖s‖).of_norm_bounded (halasz_hurwitz_difference_norm ha · hs)

lemma halasz_hurwitz_difference_differentiable {a : ℝ} (ha : 0≤a) (n : ℕ) :
    Differentiable ℂ (halaszHurwitzDifference a n) := by
  have hn : ((n+1:ℕ):ℂ)≠0 := by exact_mod_cast (show n+1≠0 by omega)
  have hna : ((((n+1:ℕ):ℝ)+a):ℂ)≠0 := by
    exact_mod_cast (show (((n+1:ℕ):ℝ)+a)≠0 from (by positivity))
  exact (differentiable_id.neg.const_cpow (Or.inl hna)).sub
    (differentiable_id.neg.const_cpow (Or.inl hn))

lemma halasz_hurwitz_difference_tsum_differentiableAt {a : ℝ}
    (ha : a∈Set.Icc (0:ℝ) 1) {s : ℂ} (hs : 0<s.re) :
    DifferentiableAt ℂ (fun z => ∑' n,halaszHurwitzDifference a n z) s := by
  let V := Metric.ball s (s.re/2)
  have hp : Summable (fun n : ℕ => (‖s‖+s.re/2)*((n+1:ℕ):ℝ)^(-(s.re/2+1))) :=
    ((Real.summable_nat_rpow.mpr (by linarith : -(s.re/2+1)< -1)).comp_injective
      Nat.succ_injective).mul_left _
  have hb : ∀ n z,z∈V → ‖halaszHurwitzDifference a n z‖≤
      (‖s‖+s.re/2)*((n+1:ℕ):ℝ)^(-(s.re/2+1)) := by
    intro n z hz
    have hdist : ‖z-s‖<s.re/2 := by simpa only [V,Metric.mem_ball,dist_eq_norm] using hz
    have hre : s.re/2<z.re := by
      have h := (Complex.abs_re_le_norm (z-s)).trans_lt hdist
      rw [Complex.sub_re] at h
      have := (abs_lt.mp h).1
      linarith
    have hn : ‖z‖≤‖s‖+s.re/2 := by
      have hh := norm_add_le (z-s) s
      rw [sub_add_cancel] at hh
      linarith
    exact (halasz_hurwitz_difference_norm ha n (by linarith)).trans
      (mul_le_mul hn
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤n+1 by omega))
          (by linarith)) (by positivity) (by positivity))
  exact (Complex.differentiableOn_tsum_of_summable_norm hp
    (fun n => (halasz_hurwitz_difference_differentiable ha.1 n).differentiableOn)
    Metric.isOpen_ball hb).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hs)))

end TwoPointCorrelations

end OAI
