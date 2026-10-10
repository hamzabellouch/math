import OAI.NumberTheory.Jacobsthal.Estimates.SecondLossIntegration

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

theorem lossTwo_measurable : Measurable (fun p : ℝ×ℝ => loss2Kernel p.2 p.1) := by
  unfold loss2Kernel
  fun_prop

theorem lossTwo_bound {x t : ℝ} (hx : x ∈ Icc (1:ℝ) 2) (ht : t ∈ Icc (1:ℝ) 2) :
    |loss2Kernel t x| ≤ 16 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have he : loss2Kernel t x=((x+2*t-2)^2*(x+2*t+4))/(12*x*t^2) := by
    unfold loss2Kernel
    field_simp
    ring
  have hs : 0 ≤ x+2*t-2 ∧ x+2*t-2 ≤ 4 := by constructor <;> linarith [hx.1,hx.2,ht.1,ht.2]
  have hs2 : (x+2*t-2)^2 ≤ 16 := by nlinarith
  have hs4 : 0 ≤ x+2*t+4 ∧ x+2*t+4 ≤ 10 := by constructor <;> linarith [hx.1,hx.2,ht.1,ht.2]
  have hnum : (x+2*t-2)^2*(x+2*t+4) ≤ 160 := by
    have h := mul_le_mul hs2 hs4.2 hs4.1 (by norm_num : (0:ℝ)≤16)
    norm_num at h
    exact h
  have ht2 : 1 ≤ t^2 := by nlinarith [ht.1]
  have hden : 12 ≤ 12*x*t^2 := by
    have h := mul_le_mul hx.1 ht2 (by norm_num : (0:ℝ)≤1) hx0.le
    nlinarith
  have hden0 : 0 < 12*x*t^2 := by positivity
  rw [he,abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hs4.1) hden0.le)]
  apply (div_le_iff₀ hden0).mpr
  nlinarith

theorem actual_second_loss_eq_L2 : omissionLossTerm 1=L2 := by
  rw [second_loss_ordered_integral]
  have h := ordered_triangle_swap lossTwo_measurable (by norm_num : (0:ℝ)≤16)
    (fun _ hx _ ht => lossTwo_bound hx ht)
  exact h

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

theorem lossThree_bound {x u t : ℝ} (hx : x ∈ Icc (1:ℝ) 2)
    (hu : u ∈ Icc (1:ℝ) 2) (ht : t ∈ Icc (1:ℝ) 2) : |loss3Kernel t u x| ≤ 64 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hu0 : 0 < u := by linarith [hu.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hs0 : 0 ≤ x+u+2*t := by positivity
  have hs8 : x+u+2*t ≤ 8 := by linarith [hx.2,hu.2,ht.2]
  have hsx : 2*x ≤ x+u+2*t := by linarith [hx.2,hu.1,ht.1]
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*x) hsx 3
  have hnum0 : 0 ≤ (x+u+2*t)^3-8*x^3 := by nlinarith
  have hp8 := pow_le_pow_left₀ hs0 hs8 3
  have hnum : (x+u+2*t)^3-8*x^3 ≤ 512 := by nlinarith [pow_nonneg hx0.le 3]
  have ht2 : 1 ≤ t^2 := by nlinarith [ht.1]
  have hxu : (1:ℝ) ≤ x*u := by simpa only [one_mul] using mul_le_mul hx.1 hu.1 (by norm_num : (0:ℝ)≤1) hx0.le
  have hprod : (1:ℝ) ≤ x*u*t^2 := by
    simpa only [one_mul] using mul_le_mul hxu ht2 (by norm_num : (0:ℝ)≤1) (mul_pos hx0 hu0).le
  have hden : 12 ≤ 12*x*u*t^2 := by nlinarith
  have hden0 : 0 < 12*x*u*t^2 := by positivity
  rw [loss3Kernel,abs_of_nonneg (div_nonneg hnum0 hden0.le)]
  apply (div_le_iff₀ hden0).mpr
  nlinarith

noncomputable def clampedThird (x u t : ℝ) : ℝ :=
  loss3Kernel (baseCutoff t) (baseCutoff u) (baseCutoff x)

theorem clampedThird_eq {x u t : ℝ} (hx : x ∈ Icc (1:ℝ) 2)
    (hu : u ∈ Icc (1:ℝ) 2) (ht : t ∈ Icc (1:ℝ) 2) :
    clampedThird x u t=loss3Kernel t u x := by
  simp only [clampedThird,baseCutoff_on hx.1 hx.2,baseCutoff_on hu.1 hu.2,baseCutoff_on ht.1 ht.2]

theorem clampedThird_bound (x u t : ℝ) : |clampedThird x u t| ≤ 64 :=
  lossThree_bound (baseCutoff_bounds x) (baseCutoff_bounds u) (baseCutoff_bounds t)

theorem clampedThird_continuous :
    Continuous (fun p : ℝ×ℝ×ℝ => clampedThird p.1 p.2.1 p.2.2) := by
  have hn : Continuous (fun p : ℝ×ℝ×ℝ =>
      (baseCutoff p.1+baseCutoff p.2.1+2*baseCutoff p.2.2)^3-8*(baseCutoff p.1)^3) := by
    unfold baseCutoff
    fun_prop
  have hd : Continuous (fun p : ℝ×ℝ×ℝ =>
      12*baseCutoff p.1*baseCutoff p.2.1*(baseCutoff p.2.2)^2) := by
    unfold baseCutoff
    fun_prop
  have hp (a : ℝ) : 0 < baseCutoff a := zero_lt_one.trans_le (baseCutoff_bounds a).1
  exact hn.div hd (fun p => ne_of_gt
    (mul_pos (mul_pos (mul_pos (by norm_num) (hp p.1)) (hp p.2.1)) (sq_pos_of_pos (hp p.2.2))))

theorem baseCutoff_continuous : Continuous baseCutoff := by unfold baseCutoff; fun_prop

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission

theorem odd_gate_indicator (H : Profile) (y : ℝ) :
    gate H .odd (2*y+2) 2=
      ∫ x : ℝ in 1..2,if x≤y then H .even (2*y+2-x) x/(max 1 x) else 0 := by
  classical
  have heq : Ioc (1:ℝ) (upperCutoff .odd (2*y+2) 2)=Ioc (1:ℝ) 2 ∩ Iic y := by
    ext x
    have hc := mem_upperCutoff .odd (2*y+2) 2 x
    constructor
    · intro hx
      obtain ⟨hx1,hx2,_hxb,ha⟩ := hc.mp hx
      rw [strong_gate_below_two hx2] at ha
      refine ⟨⟨hx1,hx2⟩,?_⟩
      change x≤y
      linarith
    · rintro ⟨⟨hx1,hx2⟩,hxy⟩
      apply hc.mpr
      refine ⟨hx1,hx2,hx2,?_⟩
      rw [strong_gate_below_two hx2]
      change x≤y at hxy
      linarith
  rw [gate,intervalIntegral.integral_of_le (upperCutoff_bounds .odd (2*y+2) 2).1,
    intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)]
  change (∫ x in Ioc (1:ℝ) (upperCutoff .odd (2*y+2) 2),H .even (2*y+2-x) x/(max 1 x))=
    ∫ x in Ioc (1:ℝ) 2,(Iic y).indicator (fun x => H .even (2*y+2-x) x/(max 1 x)) x
  rw [setIntegral_indicator measurableSet_Iic,heq]

theorem gate_force_bounds (i : Side) (r b : ℝ) :
    0 ≤ gate omissionForce i r b ∧ gate omissionForce i r b ≤ 1 := by
  have hnon := gate_nonnegative omissionForce_nonnegative i r b
  refine ⟨hnon,?_⟩
  have hb (x : ℝ) : |omissionForce i.flip (r-x) x/(max 1 x)| ≤ 1 := by
    have hd : 0 < max (1:ℝ) x := (by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 x)
    rw [abs_div,abs_of_pos hd,abs_of_nonneg (omissionForce_nonnegative _ _ _)]
    exact (div_le_one hd).mpr ((omissionForce_le_one _ _ _).trans (le_max_left 1 x))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=1) (b:=upperCutoff i r b)
    (C:=1) (f:=fun x => omissionForce i.flip (r-x) x/(max 1 x))
    (fun x _ => by simpa only [Real.norm_eq_abs] using hb x)
  have hc := upperCutoff_bounds i r b
  rw [Real.norm_eq_abs,one_mul,abs_of_nonneg (by linarith : 0 ≤ upperCutoff i r b-1)] at h
  change |gate omissionForce i r b| ≤ upperCutoff i r b-1 at h
  rw [abs_of_nonneg hnon] at h
  linarith

noncomputable def thirdKernel (p : ℝ×ℝ) : ℝ :=
  if p.2≤p.1 then (2*p.1^2/(max 1 p.2))*gate omissionForce .even (2*p.1+2-p.2) p.2 else 0

theorem thirdKernel_measurable : Measurable thirdKernel := by
  have hg := gate_continuous omissionForce_continuous .even
  have hc : Continuous (fun p : ℝ×ℝ => gate omissionForce .even (2*p.1+2-p.2) p.2) :=
    hg.comp (((continuous_const.mul continuous_fst).add continuous_const |>.sub continuous_snd).prodMk continuous_snd)
  have hp : Measurable (fun p : ℝ×ℝ => 2*p.1^2/(max 1 p.2)) := by fun_prop
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) (hp.mul hc.measurable) measurable_const

theorem thirdKernel_bound {y x : ℝ} (hy : y ∈ Icc (0:ℝ) 4) (hx : x ∈ Icc (1:ℝ) 2) :
    |thirdKernel (y,x)| ≤ 32 := by
  have hx0 : 0 < x := by linarith [hx.1]
  unfold thirdKernel
  dsimp only
  split_ifs
  · rw [max_eq_right hx.1]
    have hp0 : 0 ≤ 2*y^2/x := by positivity
    have hp32 : 2*y^2/x ≤ 32 := by
      apply (div_le_iff₀ hx0).mpr
      nlinarith [hy.1,hy.2,hx.1]
    rw [abs_of_nonneg (mul_nonneg hp0 (gate_force_bounds _ _ _).1)]
    exact (mul_le_mul_of_nonneg_left (gate_force_bounds _ _ _).2 hp0).trans (by simpa only [mul_one] using hp32)
  · norm_num

theorem third_density_kernel (y : ℝ) :
    omissionDensity 2 .odd y=∫ x : ℝ in 1..2,thirdKernel (y,x) := by
  change 2*y^2*gate (gate omissionForce) .odd (2*y+2) 2=_
  rw [odd_gate_indicator,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only [thirdKernel]
  split_ifs <;> ring

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

noncomputable def thirdInnerKernel (x : ℝ) (p : ℝ×ℝ) : ℝ :=
  (p.1^2/(max 1 p.2))*omissionForce .odd (2*p.1+2-x-p.2) p.2

theorem thirdInnerKernel_continuous (x : ℝ) : Continuous (thirdInnerKernel x) := by
  have hf : Continuous (fun p : ℝ×ℝ => omissionForce .odd (2*p.1+2-x-p.2) p.2) :=
    (omissionForce_continuous .odd).comp
      ((((continuous_const.mul continuous_fst).add continuous_const |>.sub continuous_const).sub continuous_snd).prodMk continuous_snd)
  have hp : Continuous (fun p : ℝ×ℝ => p.1^2/(max 1 p.2)) :=
    (continuous_fst.pow 2).div (continuous_const.max continuous_snd) (fun p => ne_of_gt
      ((by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 p.2)))
  exact hp.mul hf

theorem thirdInnerKernel_bound {x y u : ℝ} (hx : x ∈ Icc (1:ℝ) 2)
    (hy : y ∈ Icc x 4) (hu : u ∈ Icc (1:ℝ) x) : |thirdInnerKernel x (y,u)| ≤ 16 := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hy0 : 0 ≤ y := by linarith [hx.1,hy.1]
  have hp0 : 0 ≤ y^2/u := div_nonneg (sq_nonneg _) hu0.le
  have hp16 : y^2/u ≤ 16 := by
    apply (div_le_iff₀ hu0).mpr
    nlinarith [hy.2,hu.1]
  unfold thirdInnerKernel
  dsimp only
  rw [max_eq_right hu.1,abs_of_nonneg (mul_nonneg hp0 (omissionForce_nonnegative _ _ _))]
  exact (mul_le_mul_of_nonneg_left (omissionForce_le_one _ _ _) hp0).trans (by simpa only [mul_one] using hp16)

theorem third_even_gate (y : ℝ) {x : ℝ} (hx : x ∈ Icc (1:ℝ) 2) :
    y^2*gate omissionForce .even (2*y+2-x) x=
      ∫ u : ℝ in 1..x,thirdInnerKernel x (y,u) := by
  have hc : upperCutoff .even (2*y+2-x) x=x := baseCutoff_on hx.1 hx.2
  rw [gate,hc,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _hu
  dsimp only [thirdInnerKernel,Side.flip]
  ring

end ErdosOmissionBindings

end

end Erdos970

end OAI
