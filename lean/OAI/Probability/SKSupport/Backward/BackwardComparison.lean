import Mathlib
import OAI.Probability.SKSupport.Parabolic.FullLineComparison
import OAI.Probability.SKSupport.Moments.BurgersJets

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma bounded_linear_nonpositive {F r Ft c : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : BoundedSmoothFamily F) (hr : BoundedSmoothFamily r)
    (hcont : ∀ T, ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc (0:ℝ) T ×ˢ univ))
    (htime : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (Ft t x) t)
    (hc : ∀ t, 0 < t → ∀ x, 0 < x → c t x ≤ C)
    (hpde : ∀ t, 0 < t → ∀ x, 0 < x →
      Ft t x=(1/2:ℝ)*iteratedDeriv 2 (F t) x+r t x*deriv (F t) x+c t x*F t x)
    (hzero : ∀ t, 0 ≤ t → F t 0=0)
    (hinit : ∀ x, 0 ≤ x → F 0 x ≤ 0) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → F t x ≤ 0 := by
  obtain ⟨R,hR⟩ := hr.bound
  obtain ⟨M,hM⟩ := hF.bound
  intro T hT x hx
  have hh := Parabolic.nonnegative_halfLine_bounded
    (u := fun t x => - F t x) (ut := fun t x => -Ft t x)
    (ux := fun t x => -deriv (F t) x) (uxx := fun t x => -iteratedDeriv 2 (F t) x)
    (β := r) (c := c) (C := C) (K := (R:ℝ)) (M := (M:ℝ)) R.coe_nonneg M.coe_nonneg
    ((hcont T).neg.mono (prod_mono subset_rfl (subset_univ _)))
    (fun t _ => (hF.regular t).smooth.continuous.neg)
    (fun t ht x _ => (htime t ht.1 x).neg.hasDerivWithinAt)
    (fun t _ x _ => ((hF.regular t).smooth.differentiable (by simp) x).hasDerivAt.neg)
    (fun t _ x _ => ?_) (fun t _ x hxp => ?_)
    (fun t ht x hxp => hc t ht.1 x hxp)
    (fun t ht x hxp => ?_)
    (fun t _ x _ => neg_le_neg ((le_abs_self _).trans (hM t x)))
    (fun x hx => neg_nonneg.mpr (hinit x hx))
    (fun t ht => by rw [hzero t ht.1]; simp) T ⟨hT,le_rfl⟩ x hx
  · exact neg_nonneg.mp hh
  · have he : deriv (fun y => -F t y) = fun y => -deriv (F t) y :=
      funext (fun y => ((hF.regular t).smooth.differentiable (by simp) y).hasDerivAt.neg.deriv)
    rw [he]
    convert (hasDerivAt_spatialJet (hF.regular t).smooth 1 x).neg using 1
    first | rfl | (simp only [iteratedDeriv_one]; rfl)
  · have hb := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hR t x)) hxp.le
    have hh : x ≤ 1+x^2 := by nlinarith [sq_nonneg (x-1)]
    exact hb.trans (mul_le_mul_of_nonneg_left hh R.coe_nonneg)
  · rw [hpde t ht.1 x hxp]
    ring_nf
    exact le_rfl

namespace SmoothBurgers
variable {r : ℝ → ℝ → ℝ} (hr : SmoothBurgers r)
include hr

lemma second_odd (ho : ∀ t, Function.Odd (r t)) (t : ℝ) :
    Function.Odd (iteratedDeriv 2 (r t)) := by
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
   (even_deriv_odd ((hr.family.deriv.regular t).smooth.differentiable (by simp))
    (odd_deriv_even ((hr.family.regular t).smooth.differentiable (by simp)) (ho t)))

theorem second_nonpos (ho : ∀ t, Function.Odd (r t))
    (hi : ∀ x, 0 ≤ x → iteratedDeriv 2 (r 0) x ≤ 0) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → iteratedDeriv 2 (r t) x ≤ 0 := by
  obtain ⟨V,hV⟩ := hr.family.deriv.bound
  apply bounded_linear_nonpositive (hr.family.iteratedDeriv 2) hr.family
    (fun T => hr.jet_continuous 2 T) (fun t ht x => hr.time_derivative 2 t ht x)
    (c := fun t x => 3*deriv (r t) x) (C := 3*(V:ℝ))
  · intro t ht x hx
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hV t x)) (by norm_num)
  · intro t ht x hx
    rw [hr.rate_jet2]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    ring
  · intro t ht
    have hh := hr.second_odd ho t 0
    simp only [neg_zero] at hh
    linarith
  · exact hi

theorem rate_nonpos (ho : ∀ t, Function.Odd (r t))
    (hi : ∀ x, 0 ≤ x → burgersRate r 0 x ≤ 0) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → burgersRate r t x ≤ 0 := by
  obtain ⟨V,hV⟩ := hr.family.deriv.bound
  apply bounded_linear_nonpositive hr.rate_family hr.family hr.rate_continuous
    (fun t ht x => hr.rate_time ht x) (c := fun t x => deriv (r t) x) (C := (V:ℝ))
  · intro t ht x hx
    exact (le_abs_self _).trans (hV t x)
  · intro t ht x hx
    rfl
  · intro t ht
    have hh := hr.rate_odd ho t 0
    simp only [neg_zero] at hh
    linarith
  · exact hi

end SmoothBurgers
end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat
namespace SmoothBurgers
variable {r : ℝ → ℝ → ℝ} (hr : SmoothBurgers r)
include hr

lemma pos_halfLine (ho : ∀ t, Function.Odd (r t))
    (hv : ∀ t, 0 ≤ t → ∀ x, 0 < deriv (r t) x) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 < x) :
    0 < r t x := by
  have hm : StrictMono (r t) := strictMonoOn_univ.1 <|
    strictMonoOn_of_deriv_pos convex_univ (hr.family.regular t).smooth.continuous.continuousOn
      (fun spatial _ => hv t ht spatial)
  have hz : r t 0=0 := by
    have hh := ho t 0
    simp only [neg_zero] at hh
    linarith
  simpa only [hz] using hm hx

theorem wronskian_nonneg (ho : ∀ t, Function.Odd (r t))
    (hv : ∀ t, 0 ≤ t → ∀ x, 0 < deriv (r t) x)
    (hiw : ∀ x, 0 ≤ x → iteratedDeriv 2 (r 0) x ≤ 0)
    (hip : ∀ x, 0 ≤ x → burgersRate r 0 x ≤ 0)
    (hiK : ∀ x, 0 ≤ x → 0 ≤ backwardWronskian r 0 x) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → 0 ≤ backwardWronskian r t x := by
  have hw := hr.second_nonpos ho hiw
  have hp := hr.rate_nonpos ho hip
  obtain ⟨R,hR⟩ := hr.family.bound
  obtain ⟨M,hM⟩ := hr.wronskian_family.bound
  intro T hT x hx
  apply Parabolic.nonnegative_halfLine_bounded
    (u := backwardWronskian r) (ut := wronskianRate r)
    (ux := fun t => deriv (backwardWronskian r t))
    (uxx := fun t => iteratedDeriv 2 (backwardWronskian r t))
    (β := fun t x => r t x-deriv (r t) x/r t x)
    (c := fun t x => 2*(burgersRate r t x/r t x)) (C := 0) (K := (R:ℝ)) (M := (M:ℝ))
    R.coe_nonneg M.coe_nonneg
    ((hr.wronskian_continuous T).mono (prod_mono subset_rfl (subset_univ _)))
    (fun t _ => (hr.wronskian_family.regular t).smooth.continuous)
    (fun t ht x _ => (hr.wronskian_time ht.1 x).hasDerivWithinAt)
    (fun t _ x _ => ((hr.wronskian_family.regular t).smooth.differentiable (by simp) x).hasDerivAt)
    (fun t _ x _ => by simpa only [iteratedDeriv_one] using
      hasDerivAt_spatialJet (hr.wronskian_family.regular t).smooth 1 x)
    (fun t ht x hx => ?_) (fun t ht x hx => ?_) (fun t ht x hx => ?_)
    (fun t _ x _ => (neg_le_neg (hM t x)).trans (neg_abs_le _)) hiK
    (fun t ht => ?_) T ⟨hT,le_rfl⟩ x hx
  · have hpos := hr.pos_halfLine ho hv ht.1.le hx
    have hsub : 0 ≤ deriv (r t) x/r t x*x :=
      mul_nonneg (div_nonneg (hv t ht.1.le x).le hpos.le) hx.le
    have hb := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hR t x)) hx.le
    have hxx : x ≤ 1+x^2 := by nlinarith [sq_nonneg (x-1)]
    have hlast := mul_le_mul_of_nonneg_left hxx R.coe_nonneg
    nlinarith
  · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (div_nonpos_of_nonpos_of_nonneg (hp t ht.1.le x hx.le) (hr.pos_halfLine ho hv ht.1.le hx).le)
  · rw [hr.wronskian_equation t x (ne_of_gt (hr.pos_halfLine ho hv ht.1.le hx))]
    exact mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (hr.pos_halfLine ho hv ht.1.le hx).le (hw t ht.1.le x hx.le))
      (hp t ht.1.le x hx.le)
  · have hh := hr.wronskian_odd ho t 0
    simp only [neg_zero] at hh
    linarith

end SmoothBurgers
end ZeroTemperatureSK.Heat

end
end

end OAI
