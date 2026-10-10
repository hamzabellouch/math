import Mathlib

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma linear_supports_match {f : E → ℝ} {x : E} {L U : E →L[ℝ] ℝ} {B : ℝ}
    (hnear : ∀ᶠ y in 𝓝 x,
      f x+L (y-x)-B*‖y-x‖^2≤f y ∧ f y≤f x+U (y-x)+B*‖y-x‖^2) : L=U := by
  have hmin : IsLocalMin (fun h : E => (U-L) h+(2*B)*‖h‖^2) 0 := by
    have hn := ((continuous_const.add continuous_id).tendsto (0:E)).eventually
      (show ∀ᶠ y in 𝓝 (x+(0:E)), _ from by simpa only [add_zero] using hnear)
    filter_upwards [hn] with h hh
    change f x + L (x+h-x) - B*‖x+h-x‖^2 ≤ f (x+h) ∧
      f (x+h) ≤ f x + U (x+h-x) + B*‖x+h-x‖^2 at hh
    simp only [add_sub_cancel_left] at hh
    simpa only [add_sub_cancel_left] using
      (show (U-L) 0+(2*B)*‖(0:E)‖^2≤(U-L) h+(2*B)*‖h‖^2 from by
        simp only [map_zero,norm_zero,zero_pow (by omega : 2≠0),mul_zero,zero_add,
          _root_.sub_apply]
        linarith [hh.1,hh.2])
  have hd : HasFDerivAt (fun h : E => (U-L) h+(2*B)*‖h‖^2) (U-L) 0 := by
    convert (U-L).hasFDerivAt.add ((hasStrictFDerivAt_norm_sq (0:E)).hasFDerivAt.const_mul (2*B)) using 1
    all_goals first | rfl | (ext h; simp)
  exact (sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hd)).symm

lemma hasFDerivAt_of_quadratic_remainder {f : E → ℝ} {x : E} {L : E →L[ℝ] ℝ}
    {B : ℝ} (hB : 0≤B)
    (hnear : ∀ᶠ y in 𝓝 x, |f y-f x-L (y-x)|≤B*‖y-x‖^2) :
    HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have hn : ∀ᶠ h : E in 𝓝 0, |f (x+h)-f x-L h|≤B*‖h‖^2 := by
    simpa only [add_zero,add_sub_cancel_left] using
      ((show Tendsto (fun h : E => x+h) (𝓝 0) (𝓝 x) from by
        convert (continuous_const.add continuous_id : Continuous (fun h : E => x+h)).tendsto 0 using 1
        all_goals first | rfl | simp).eventually hnear)
  have hr : ∀ᶠ h : E in 𝓝 0, ‖h‖<ε/(B+1) :=
    (continuous_norm.tendsto (0:E)).eventually (by
      simpa only [norm_zero] using eventually_lt_nhds (show (0:ℝ)<ε/(B+1) by positivity))
  filter_upwards [hn,hr] with h hh hr
  rw [Real.norm_eq_abs]
  apply hh.trans
  have hmul : (B+1)*‖h‖<ε := by
    have := (lt_div_iff₀ (show 0<B+1 by linarith)).mp hr
    nlinarith
  have hh0 := norm_nonneg h
  have : B*‖h‖≤ε := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hh0]

lemma quadratic_remainder_of_two_supports {f : E → ℝ} {S : Set E}
    (hS : IsOpen S) {B : ℝ} (hB : 0≤B)
    (hs : ∀ x∈S, ∃ L U : E →L[ℝ] ℝ, ∀ y∈S,
      f x+L (y-x)-B*‖y-x‖^2≤f y ∧ f y≤f x+U (y-x)+B*‖y-x‖^2) :
    ∀ x∈S, DifferentiableAt ℝ f x ∧
      ∀ y∈S, |f y-f x-fderiv ℝ f x (y-x)|≤B*‖y-x‖^2 := by
  intro x hx
  obtain ⟨L,U,hLU⟩ := hs x hx
  have hsame : L=U := linear_supports_match
    (by filter_upwards [hS.mem_nhds hx] with y hy; exact hLU y hy)
  subst U
  have hrem : ∀ y∈S, |f y-f x-L (y-x)|≤B*‖y-x‖^2 := by
    intro y hy
    exact abs_le.mpr ⟨by linarith [(hLU y hy).1],by linarith [(hLU y hy).2]⟩
  have hd := hasFDerivAt_of_quadratic_remainder hB
    (by filter_upwards [hS.mem_nhds hx] with y hy; exact hrem y hy)
  exact ⟨hd.differentiableAt,by simpa only [hd.fderiv] using hrem⟩

lemma derivative_lipschitz_of_quadratic_remainder {f : E → ℝ} {a : E} {r B : ℝ}
    (hr : 0<r) (hB : 0≤B)
    (hrem : ∀ x∈ball a r, ∀ y∈ball a r,
      |f y-f x-fderiv ℝ f x (y-x)|≤B*‖y-x‖^2) :
    LipschitzOnWith ⟨6*B,by positivity⟩ (fderiv ℝ f) (ball a (r/4)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm,dist_eq_norm]
  change ‖fderiv ℝ f x-fderiv ℝ f y‖≤(6*B)*‖x-y‖
  by_cases hxy : x=y
  · simp only [hxy,sub_self,norm_zero,mul_zero,le_refl]
  let d := ‖x-y‖
  have hd : 0<d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hdR : d<r/2 := by
    have H := dist_triangle x a y
    rw [dist_comm a y] at H
    change dist x a<r/4 at hx
    change dist y a<r/4 at hy
    rw [dist_eq_norm] at H
    change d≤_ at H
    linarith
  have hxR : x∈ball a r := ball_subset_ball (by linarith only [hr]) hx
  have hyR : y∈ball a r := ball_subset_ball (by linarith) hy
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  let z := x+d • e
  have hzR : z∈ball a r := by
    have H := dist_triangle z x a
    have hzx : dist z x=d := by simp only [z,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hd,he,mul_one]
    rw [hzx] at H
    change dist x a<r/4 at hx
    exact lt_of_le_of_lt H (by linarith)
  have hzx : ‖z-x‖=d := by simp only [z,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hd,he,mul_one]
  have hzy : ‖z-y‖≤2*d := by
    have H := norm_add_le (z-x) (x-y)
    have he : (z-x)+(x-y)=z-y := by abel
    rw [he,hzx] at H
    change _≤d+d at H
    linarith
  have hxz := hrem x hxR z hzR
  have hyz := hrem y hyR z hzR
  have hyx := hrem y hyR x hxR
  have hlin : (fderiv ℝ f x-fderiv ℝ f y) (z-x) =
      (f z-f y-fderiv ℝ f y (z-y))-
      (f x-f y-fderiv ℝ f y (x-y))-
      (f z-f x-fderiv ℝ f x (z-x)) := by
    have he : z-y=(z-x)+(x-y) := by abel
    rw [he,map_add,_root_.sub_apply]
    ring
  have H := abs_sub ((f z-f y-fderiv ℝ f y (z-y))-
      (f x-f y-fderiv ℝ f y (x-y))) (f z-f x-fderiv ℝ f x (z-x))
  have H' := abs_sub (f z-f y-fderiv ℝ f y (z-y)) (f x-f y-fderiv ℝ f y (x-y))
  rw [←hlin] at H
  rw [hzx] at hxz
  have Hsq : ‖z-y‖^2≤4*d^2 := by nlinarith [norm_nonneg (z-y)]
  have Hb := mul_le_mul_of_nonneg_left Hsq hB
  have hbound : |(fderiv ℝ f x-fderiv ℝ f y) (z-x)|≤6*B*d^2 := by
    change _≤B*d^2 at hyx
    nlinarith
  have happly : (fderiv ℝ f x-fderiv ℝ f y) (z-x)=d*((fderiv ℝ f x-fderiv ℝ f y) e) := by
    simp only [z,add_sub_cancel_left,map_smul,smul_eq_mul]
  rw [happly,abs_mul,abs_of_pos hd] at hbound
  rw [Real.norm_eq_abs]
  nlinarith

end WeakMTWTransport

end

end OAI
