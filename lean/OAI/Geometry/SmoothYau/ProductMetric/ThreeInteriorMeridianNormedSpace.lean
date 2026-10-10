import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ThreeRankNormedSpace

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeInteriorMeridianNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeInteriorMeridianContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
local instance threeInteriorMeridian_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩

def threeInteriorMeridianAmbient (t : ℝ) : Euclidean 3 := Real.cos t • productAxis 1+Real.sin t • productAxis 2
lemma threeInteriorMeridianAmbient_norm (t : ℝ) : ‖threeInteriorMeridianAmbient t‖=1 := by
  have hn : ‖threeInteriorMeridianAmbient t‖^2=1 := by
    rw [←real_inner_self_eq_norm_sq]
    simp only [threeInteriorMeridianAmbient,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,productAxis_inner]
    norm_num [Fin.ext_iff]
    nlinarith [Real.sin_sq_add_cos_sq t]
  nlinarith [norm_nonneg (threeInteriorMeridianAmbient t)]
def threeInteriorMeridian (t : ℝ) : ThreeManifold :=
  (⟨threeInteriorMeridianAmbient t,by simpa only [mem_sphere,dist_zero_right] using threeInteriorMeridianAmbient_norm t⟩,1)
lemma threeInteriorMeridian_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ThreeModel) ∞ threeInteriorMeridian := by
  have h : ContDiff ℝ ∞ threeInteriorMeridianAmbient :=
    (Real.contDiff_cos.smul contDiff_const).add (Real.contDiff_sin.smul contDiff_const)
  have hs := h.contMDiff.codRestrict_sphere (n:=2) (fun t => (threeInteriorMeridian t).1.property)
  apply contMDiff_reModel_target threeModelEquiv
  rw [modelWithCornersSelf_prod]
  exact hs.prodMk contMDiff_const
lemma threeInteriorMeridian_A (t : ℝ) : productA (threeInteriorMeridian t).1=((Real.cos t:ℝ):ℂ)*Complex.I := by
  apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,mul_one] <;> simp [productA_re,productA_im,threeInteriorMeridian,threeInteriorMeridianAmbient,productAxis]
lemma threeInteriorMeridian_B (t : ℝ) : productB (threeInteriorMeridian t).1=((Real.sin t:ℝ):ℂ)*Complex.I := by
  apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,mul_one] <;> simp [productB_re,productB_im,threeInteriorMeridian,threeInteriorMeridianAmbient,productAxis]
lemma threeInteriorMeridian_circle (t : ℝ) : ((threeInteriorMeridian t).2:ℂ)=1 := by rfl
lemma interior_complex_I_pow_four_add_one (m : ℕ) : Complex.I^(4*m+1)=Complex.I := by
  rw [pow_add,pow_mul]
  norm_num
lemma interior_complex_I_pow_four (m : ℕ) : Complex.I^(4*m)=1 := by rw [pow_mul]; norm_num
lemma interior_complex_neg_one_pow_four_add_one (m : ℕ) : (-1:ℂ)^(4*m+1)=-1 := by
  rw [pow_add,pow_mul]
  norm_num
lemma threeInteriorMeridian_complex (r t : ℝ) (m : ℕ) :
    threeCoupledComplex r (4*m+1) (threeInteriorMeridian t)=
      (((Real.cos t)^(4*m+1)+r^(4*m+1)*(Real.sin t)^(4*m+1):ℝ):ℂ)*Complex.I := by
  simp only [threeCoupledComplex,threeInteriorMeridian_A,threeInteriorMeridian_B,threeInteriorMeridian_circle,mul_pow,
    interior_complex_I_pow_four_add_one,one_pow]
  simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]
  ring
lemma threeInteriorMeridian_zero (r t : ℝ) (m : ℕ) : threeCoupled r (4*m+1) (threeInteriorMeridian t)=0 := by
  rw [threeCoupled,threeInteriorMeridian_complex]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]
lemma threeInteriorMeridian_gradient_value (r t : ℝ) (m : ℕ) :
    coordinateGradientPair threeBackgroundMetric (threeCoupled r (4*m+1))
      (threeCoupled r (4*m+1)) (threeInteriorMeridian t)=
      (4*(m:ℝ)+1)^2*(((Real.cos t)^(4*m)+r^(4*m+1)*(Real.sin t)^(4*m))^2+
        ((Real.cos t)^(4*m+1)+r^(4*m+1)*(Real.sin t)^(4*m+1))^2) := by
  rw [threeCoupled_gradient_value r (4*m+1) (by omega),threeInteriorMeridian_zero,threeInteriorMeridian_complex,
    threeInteriorMeridian_A,threeInteriorMeridian_B,threeInteriorMeridian_circle]
  simp only [Nat.add_sub_cancel,mul_pow,interior_complex_I_pow_four,one_pow]
  simp only [←Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.one_re,Complex.one_im,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  ring
def threeInteriorMeridianEnergy (r : ℝ) (m : ℕ) : ℝ → ℝ :=
  coordinateGradientPair threeBackgroundMetric (threeCoupled r (4*m+1))
    (threeCoupled r (4*m+1)) ∘ threeInteriorMeridian
lemma threeInteriorMeridianEnergy_smooth (r : ℝ) (m : ℕ) : ContDiff ℝ ∞ (threeInteriorMeridianEnergy r m) :=
  ((contMDiff_coordinateGradientPair (threeCoupled_smooth r _) (threeCoupled_smooth r _)
    threeBackgroundMetric).comp threeInteriorMeridian_smooth).contDiff
lemma threeInteriorMeridianEnergy_zero (r : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    threeInteriorMeridianEnergy r m 0=2*(4*(m:ℝ)+1)^2 := by
  rw [threeInteriorMeridianEnergy,Function.comp_apply,threeInteriorMeridian_gradient_value]
  simp [show 4*m≠0 by omega]
  ring
lemma threeInteriorMeridianEnergy_right (r : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    threeInteriorMeridianEnergy r m (Real.pi/2)=2*(4*(m:ℝ)+1)^2*(r^(4*m+1))^2 := by
  rw [threeInteriorMeridianEnergy,Function.comp_apply,threeInteriorMeridian_gradient_value]
  simp [show 4*m≠0 by omega]
  ring
lemma exists_threeInteriorMeridianEnergy_deriv (r : ℝ) (hr : 0<r) (hr1 : r<1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c ∈ Ioo 0 (Real.pi/2), deriv (threeInteriorMeridianEnergy r m) c ≠ 0 := by
  have hd := (threeInteriorMeridianEnergy_smooth r m).differentiable (by simp)
  obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope (threeInteriorMeridianEnergy r m) (by positivity : (0:ℝ)<Real.pi/2)
    (threeInteriorMeridianEnergy_smooth r m).continuous.continuousOn hd.differentiableOn
  refine ⟨c,hc,?_⟩
  rw [he,div_ne_zero_iff,sub_ne_zero]
  constructor
  · rw [threeInteriorMeridianEnergy_right r hm,threeInteriorMeridianEnergy_zero r hm]
    have hp : (r^(4*m+1))^2<1 := by
      rw [←pow_mul]
      exact pow_lt_one₀ hr.le hr1 (by omega)
    have hk : 0<2*(4*(m:ℝ)+1)^2 := by positivity
    nlinarith
  · linarith [Real.pi_pos]
lemma threeInteriorMeridian_circle_deriv_ne (r : ℝ) (hr : 0<r) (m : ℕ) {c : ℝ}
    (hc : c ∈ Ioo 0 (Real.pi/2)) :
    fderiv ℝ (threeCoupled r (4*m+1) ∘ (chartAt ThreeModel (threeInteriorMeridian c)).symm) 0
      (threeCircleDirection (threeInteriorMeridian c)) ≠ 0 := by
  rw [threeCoupled_circle_direction r (4*m+1) (by omega),threeInteriorMeridian_complex]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero]
  have hcos : 0<Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hc.1],hc.2⟩
  have hsin : 0<Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hk : (0:ℝ)<(4*m+1:ℕ) := by positivity
  exact mul_ne_zero (neg_ne_zero.mpr hk.ne') (by positivity)
lemma exists_threeCoupled_interior_gradient_rank (r : ℝ) (hr : 0<r) (hr1 : r<1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c ∈ Ioo 0 (Real.pi/2), Function.Surjective (fderiv ℝ
      (fun y => (threeCoupled r (4*m+1) ((chartAt ThreeModel (threeInteriorMeridian c)).symm y),
        coordinateGradientPair threeBackgroundMetric (threeCoupled r (4*m+1))
          (threeCoupled r (4*m+1)) ((chartAt ThreeModel (threeInteriorMeridian c)).symm y))) 0) := by
  obtain ⟨c,hc,hR⟩ := exists_threeInteriorMeridianEnergy_deriv r hr hr1 hm
  refine ⟨c,hc,?_⟩
  let e := chartAt ThreeModel (threeInteriorMeridian c)
  let u := threeCoupled r (4*m+1)
  let R := coordinateGradientPair threeBackgroundMetric u u
  have hu := threeCoupled_smooth r (4*m+1)
  have hRs := contMDiff_coordinateGradientPair hu hu threeBackgroundMetric
  have ht : (0:ThreeModel) ∈ e.target := by rw [three_chart_target]; trivial
  have hud := (contDiffAt_inChart hu (threeInteriorMeridian c) ht).differentiableAt (by simp)
  have hRd := (contDiffAt_inChart hRs (threeInteriorMeridian c) ht).differentiableAt (by simp)
  change Function.Surjective (fderiv ℝ (fun y => ((u ∘ e.symm) y,(R ∘ e.symm) y)) 0)
  rw [hud.fderiv_prodMk hRd]
  apply linear_prod_surjective_of_directions _ _ (threeCircleDirection (threeInteriorMeridian c))
    (deriv (e ∘ threeInteriorMeridian) c)
  · exact threeInteriorMeridian_circle_deriv_ne r hr m hc
  · have hh := inChart_deriv_curve threeInteriorMeridian_smooth hu c
    rw [three_chart_center] at hh
    have hz : u ∘ threeInteriorMeridian = fun _ => 0 := funext (fun t => threeInteriorMeridian_zero r t m)
    change fderiv ℝ (u ∘ e.symm) 0 (deriv (e ∘ threeInteriorMeridian) c)=deriv (u ∘ threeInteriorMeridian) c at hh
    simpa only [hz,deriv_const] using hh
  · have hh := inChart_deriv_curve threeInteriorMeridian_smooth hRs c
    rw [three_chart_center] at hh
    exact hh.trans_ne hR

end YauCounterexamples
end

end OAI
