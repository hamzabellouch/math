import OAI.NumberTheory.TwoPoint.Halasz.HalaszHurwitzDifference
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakHurwitzGrowth
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! Continuation of the normally convergent shifted difference series.
The equality concerns the library Hurwitz zeta and its exact first term. -/
namespace TwoPointCorrelations

open Complex HurwitzZeta Filter
open scoped Topology

lemma halasz_hurwitz_first_term_differentiable (a : ℝ) :
    Differentiable ℂ (mrtHurwitzFirstTerm a) := by
  intro s
  change DifferentiableAt ℂ (fun z => if a=0 then 0 else (a:ℂ)^(-z)) s
  by_cases ha : a=0
  · simp only [ite_eq_left ha]
    exact differentiableAt_const (c := (0:ℂ))
  · simp only [ite_eq_right ha]
    exact differentiableAt_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr ha))

lemma halasz_hurwitz_difference_series_convergent {a : ℝ}
    (ha : a∈Set.Icc (0:ℝ) 1) {s : ℂ} (hs : 1<s.re) :
    (∑' n,halaszHurwitzDifference a n s)=
      hurwitzZeta (a:UnitAddCircle) s-riemannZeta s-mrtHurwitzFirstTerm a s := by
  let f : ℕ → ℂ := fun n => 1/((n:ℝ)+a:ℂ)^s
  have hf := hasSum_hurwitzZeta_of_one_lt_re ha hs
  have hf' : Summable f := hf.summable
  have hshift : Summable (fun n => f (n+1)) := hf'.comp_injective Nat.succ_injective
  have hzero : f 0=mrtHurwitzFirstTerm a s := by
    by_cases ha0 : a=0
    · simp [f,mrtHurwitzFirstTerm,ha0,zero_cpow (ne_zero_of_one_lt_re hs)]
    · simp [f,mrtHurwitzFirstTerm,ha0,cpow_neg]
  have htail : (∑' n,f (n+1))=hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s := by
    have hEq := hf'.tsum_eq_zero_add
    have ht := hf.tsum_eq
    change (∑' n,f n)=_ at ht
    rw [ht,hzero] at hEq
    linear_combination -hEq
  have hg : Summable (fun n : ℕ => 1/((n+1:ℕ):ℂ)^s) :=
    (Complex.summable_one_div_nat_cpow.mpr hs).comp_injective Nat.succ_injective
  have hzt : (∑' n : ℕ,1/((n+1:ℕ):ℂ)^s)=riemannZeta s := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (zeta_eq_tsum_one_div_nat_add_one_cpow hs).symm
  calc
    _ = (∑' n,f (n+1))-(∑' n : ℕ,1/((n+1:ℕ):ℂ)^s) := by
      rw [← Summable.tsum_sub hshift hg]
      apply tsum_congr
      intro n
      simp only [halaszHurwitzDifference,f,one_div,cpow_neg]
    _ = _ := by rw [htail,hzt]; ring

theorem halasz_hurwitz_difference_series {a : ℝ}
    (ha : a∈Set.Icc (0:ℝ) 1) {s : ℂ} (hs : 0<s.re) :
    (∑' n,halaszHurwitzDifference a n s)=
      hurwitzZeta (a:UnitAddCircle) s-riemannZeta s-mrtHurwitzFirstTerm a s := by
  let U : Set ℂ := {z | 0<z.re}
  let F : ℂ → ℂ := fun z =>
    hurwitzZeta (a:UnitAddCircle) z-riemannZeta z-mrtHurwitzFirstTerm a z
  let G : ℂ → ℂ := fun z => ∑' n,halaszHurwitzDifference a n z
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hc : Convex ℝ U := (convex_Ioi (0:ℝ)).linear_preimage Complex.reLm
  have hd : Differentiable ℂ F := by
    intro z
    dsimp only [F]
    rw [← hurwitzZeta_zero]
    exact ((differentiable_hurwitzZeta_sub_hurwitzZeta (a:UnitAddCircle) 0) z).sub
      (halasz_hurwitz_first_term_differentiable a z)
  have hF : AnalyticOnNhd ℂ F U := hd.differentiableOn.analyticOnNhd ho
  have hG : AnalyticOnNhd ℂ G U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    exact (halasz_hurwitz_difference_tsum_differentiableAt ha hz).differentiableWithinAt
  have heq : F=ᶠ[𝓝 (2:ℂ)] G := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1<(2:ℂ).re by norm_num)] with z hz
    exact (halasz_hurwitz_difference_series_convergent ha hz).symm
  exact (hF.eqOn_of_preconnected_of_eventuallyEq hG hc.isPreconnected
    (show (2:ℂ)∈U by change 0<(2:ℂ).re; norm_num) heq hs).symm

end TwoPointCorrelations

end OAI
