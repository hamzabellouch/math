import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatVarianceDerivative
import OAI.Geometry.WeakHessian.LocalBounds.VarianceContinuity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile136
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.cheegerHeat_reversePoincare_integral {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) (n : ℕ) (hfb : ∀ x,|f x| ≤ (n:ℝ))
    (ρ : Lp ℝ 2 m) (hρi : Integrable ρ m) (hρn : ∀ᵐ x ∂m,0 ≤ ρ x)
    {C : ℝ} (hC : 0 ≤ C) (hρb : ∀ᵐ x ∂m,|ρ x| ≤ C) {t : ℝ} (ht : 0 < t) :
    2*t*Real.exp (-2*|K| *t)*(∫ x,ρ x*(weakGradient m (cheegerHeat h t (hf2.toLp f) : X → ℝ) x)^2 ∂m) ≤
      (n:ℝ)^2*(∫ x,ρ x ∂m) := by
  let u := hf2.toLp f
  let β (s : ℝ) := ∫ x,(cheegerHeat h s u x)^2*cheegerHeat h (t-s) ρ x ∂m
  let G := ∫ x,ρ x*(weakGradient m (cheegerHeat h t u : X → ℝ) x)^2 ∂m
  let c := Real.exp (-2*|K| *t)
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have huB : ∀ᵐ x ∂m,|u x| ≤ (n:ℝ) := by
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [show u x=f x from hx]
    exact hfb x
  have hρupper : ∀ᵐ x ∂m,ρ x ≤ C := hρb.mono fun _ hx => (le_abs_self _).trans hx
  have hcomp (s : ℝ) (hs : 0 < s) (hst : s < t) : c*G ≤
      ∫ x,cheegerHeat h (t-s) ρ x*(weakGradient m (cheegerHeat h s u : X → ℝ) x)^2 ∂m := by
    obtain ⟨A,hA,-⟩ := cheegerHeat_deriv_at_positive hfin h u hs
    have hS := (hrcd.1.global_isLaplacian_of_formGenerator hfin o h _ _ hA).1
    let D := hS.2.2.toLp (weakGradient m (cheegerHeat h s u : X → ℝ))
    have hD : IsMinimalLocalWeakUpperGradient m (cheegerHeat h s u : X → ℝ) D :=
      (weakGradient_isMinimal hS.2.1.2).congr_ae .rfl hS.2.2.coeFn_toLp.symm
    have HG := hrcd.cheegerHeat_gradient_integral hN hfull hfin h o hD (sub_pos.mpr hst).le ρ hρi hρn hC hρupper
    have he : cheegerHeat h (t-s) (cheegerHeat h s u) = cheegerHeat h t u := by
      have H := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
        (cheegerHeat_add h (sub_pos.mpr hst).le hs.le)
      simpa only [sub_add_cancel,mul_apply_eq_comp] using H.symm
    rw [he] at HG
    have heD : (∫ x,cheegerHeat h (t-s) ρ x*(D x)^2 ∂m) =
        ∫ x,cheegerHeat h (t-s) ρ x*(weakGradient m (cheegerHeat h s u : X → ℝ) x)^2 ∂m := by
      apply integral_congr_ae
      filter_upwards [hS.2.2.coeFn_toLp] with x hx
      rw [show D x=weakGradient m (cheegerHeat h s u : X → ℝ) x from hx]
    rw [heD] at HG
    have hn : 0 ≤ ∫ x,cheegerHeat h (t-s) ρ x*(weakGradient m (cheegerHeat h s u : X → ℝ) x)^2 ∂m :=
      integral_nonneg_of_ae ((cheegerHeat_nonneg h (sub_pos.mpr hst).le ρ hρn).mono fun _ hx => mul_nonneg hx (sq_nonneg _))
    have hex : c*Real.exp (-2*K*(t-s)) ≤ 1 := by
      rw [show c=Real.exp (-2*|K| *t) from rfl,← Real.exp_add,← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have ha : -|K| ≤ K := neg_abs_le K
      have hb : 0 ≤ |K| := abs_nonneg K
      nlinarith [mul_nonneg (show 0 ≤ K+|K| by linarith) (sub_pos.mpr hst).le, mul_nonneg hb hs.le]
    have HH := mul_le_mul_of_nonneg_left HG hc
    dsimp only [G] at *
    calc
      _ ≤ c*(Real.exp (-2*K*(t-s))*_) := HH
      _ = (c*Real.exp (-2*K*(t-s)))*_ := by ring
      _ ≤ _ := mul_le_of_le_one_left hn hex
  have hd (s : ℝ) (hs : s ∈ interior (Icc (0:ℝ) t)) : HasDerivAt β
      (-2*(∫ x,cheegerHeat h (t-s) ρ x*(weakGradient m (cheegerHeat h s u : X → ℝ) x)^2 ∂m)) s := by
    rw [interior_Icc] at hs
    exact hrcd.cheegerHeat_variance_derivative hN hfull hfin h o hf hf2 n hfb ρ hC hρb hs.1 hs.2
  have HB := (convex_Icc (0:ℝ) t).image_sub_le_mul_sub_of_deriv_le
    (cheegerHeat_variance_continuousOn hfin h u ρ n huB t)
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (C := -2*(c*G)) (fun s hs => by
      rw [(hd s hs).deriv]
      rw [interior_Icc] at hs
      linarith only [hcomp s hs.1 hs.2])
    0 ⟨le_rfl,ht.le⟩ t ⟨ht.le,le_rfl⟩ ht.le
  have hmass := hrcd.1.cheegerHeat_mass_nonneg hN hfull hfin o h ρ hρn hρi ht.le
  have hb0 : β 0 ≤ (n:ℝ)^2*(∫ x,ρ x ∂m) := by
    have hup : Integrable (fun x => (u x)^2*cheegerHeat h t ρ x) m := by
      simpa only [mul_comm] using integrable_bounded_Lp_sq (Lp.memLp (cheegerHeat h t ρ)).aestronglyMeasurable
        (cheegerHeat_bounded h ht.le hC ρ hρb) u
    have HI := integral_mono_ae hup (hmass.1.const_mul ((n:ℝ)^2)) (by
      filter_upwards [huB,cheegerHeat_nonneg h ht.le ρ hρn] with x hb hn
      apply mul_le_mul_of_nonneg_right _ hn
      have HH := (sq_le_sq₀ (abs_nonneg (u x)) (Nat.cast_nonneg n)).mpr hb
      simpa only [sq_abs] using HH)
    rw [integral_const_mul,hmass.2] at HI
    simpa only [β,zero_sub,sub_zero,cheegerHeat_zero,one_apply_eq_self] using HI
  have hbt : 0 ≤ β t := by
    apply integral_nonneg_of_ae
    filter_upwards [cheegerHeat_nonneg h (show 0 ≤ t-t by simp) ρ hρn] with x hx
    exact mul_nonneg (sq_nonneg _) hx
  change 2*t*c*G ≤ _
  change β t-β 0 ≤ -2*(c*G)*(t-0) at HB
  nlinarith only [HB,hb0,hbt]
end WeakHessian

end
end InlinedFile136

end OAI
