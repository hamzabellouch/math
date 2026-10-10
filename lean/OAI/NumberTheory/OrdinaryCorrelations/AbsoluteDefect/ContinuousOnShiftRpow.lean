import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set

namespace OrdinaryHalaszEnvelopes

lemma continuousOn_shift_rpow {δ r : ℝ} (hδ : 0<δ) :
    ContinuousOn (fun x : ℝ => (δ+x)^r) (Icc 0 1) := by
  apply (continuousOn_const.add continuousOn_id).rpow_const
  intro x hx
  left
  change δ+x ≠ 0
  linarith [hx.1]

lemma integral_shift_rpow {δ r : ℝ} (hδ : 0<δ) (hr : r≠-1) :
    (∫ x in Icc (0:ℝ) 1, (δ+x)^r) = ((δ+1)^(r+1)-δ^(r+1))/(r+1) := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => x^r) δ]
  simp only [add_zero]
  apply integral_rpow
  right
  refine ⟨hr,?_⟩
  rw [uIcc_of_le (by linarith : δ≤δ+1)]
  simp only [Set.mem_Icc,not_and]
  intro h
  linarith

lemma integral_inverse_sqrt {δ : ℝ} (hδ : 0<δ) :
    (∫ x in Icc (0:ℝ) 1, (δ+x)^(-(1/2:ℝ))) ≤ 2*Real.sqrt (δ+1) := by
  rw [integral_shift_rpow hδ (by norm_num)]
  norm_num
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
  nlinarith [Real.sqrt_nonneg δ]

lemma integral_inverse_cube {δ : ℝ} (hδ : 0<δ) :
    (∫ x in Icc (0:ℝ) 1, (δ+x)^(-(3/2:ℝ))) ≤ 2/Real.sqrt δ := by
  rw [integral_shift_rpow hδ (by norm_num)]
  norm_num
  have h1 : 0≤δ+1 := by linarith
  rw [Real.rpow_neg h1,Real.rpow_neg hδ.le,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
  have hn := inv_nonneg.mpr (Real.sqrt_nonneg (δ+1))
  simp only [div_eq_mul_inv]
  nlinarith

lemma sqrt_energy_le {C u : ℝ} (hC : 0≤C) (hu : 0<u) (hu2 : u≤2) :
    Real.sqrt (C*(2+1/u)) ≤ Real.sqrt (5*C)*u^(-(1/2:ℝ)) := by
  have hraw : C*(2+1/u)≤5*C/u := by
    apply (le_div_iff₀ hu).mpr
    have hi : (1/u)*u=1 := one_div_mul_cancel hu.ne'
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hu2)]
  calc
    _ ≤ Real.sqrt (5*C/u) := Real.sqrt_le_sqrt hraw
    _ = _ := by rw [Real.sqrt_div (by positivity),Real.rpow_neg hu.le,←Real.sqrt_eq_rpow,div_eq_mul_inv]

lemma envelope_identity {u ε B : ℝ} (hu : 0<u) :
    (ε/u+B)*u^(-(1/2:ℝ)) = ε*u^(-(3/2:ℝ))+B*u^(-(1/2:ℝ)) := by
  rw [add_mul]
  congr 1
  rw [div_eq_mul_inv,mul_assoc,←Real.rpow_neg_one u,←Real.rpow_add hu]
  norm_num

lemma envelope_integral {C δ ε B : ℝ} (hC : 0≤C) (hδ : 0<δ)
    (hδ1 : δ≤1) (hε : 0≤ε) (hB : 0≤B) :
    (∫x in Icc (0:ℝ) 1, (ε/(δ+x)+B)*Real.sqrt (C*(2+1/(δ+x)))) ≤
      Real.sqrt (5*C)*(ε*(2/Real.sqrt δ)+B*(2*Real.sqrt (δ+1))) := by
  have hu (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : 0<δ+x := by linarith [hx.1]
  have hi1 := (continuousOn_shift_rpow (r:=-(3/2:ℝ)) hδ).integrableOn_Icc («μ» := volume)
  have hi2 := (continuousOn_shift_rpow (r:=-(1/2:ℝ)) hδ).integrableOn_Icc («μ» := volume)
  have hc : ContinuousOn (fun x : ℝ => (ε/(δ+x)+B)*Real.sqrt (C*(2+1/(δ+x)))) (Icc 0 1) := by
    apply ContinuousOn.mul
    · exact (continuousOn_const.div (continuousOn_const.add continuousOn_id) (fun x hx => (hu x hx).ne')).add continuousOn_const
    · apply ContinuousOn.sqrt
      exact continuousOn_const.mul (continuousOn_const.add (continuousOn_const.div
        (continuousOn_const.add continuousOn_id) (fun x hx => (hu x hx).ne')))
  calc
    _ ≤ ∫x in Icc (0:ℝ) 1, Real.sqrt (5*C)*(ε*(δ+x)^(-(3/2:ℝ))+B*(δ+x)^(-(1/2:ℝ))) := by
      apply integral_mono_ae hc.integrableOn_Icc (((hi1.const_mul ε).add (hi2.const_mul B)).const_mul (Real.sqrt (5*C)))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have he := mul_le_mul_of_nonneg_left (sqrt_energy_le hC (hu x hx) (by linarith [hx.2]))
        (add_nonneg (div_nonneg hε (hu x hx).le) hB)
      calc
        _ ≤ _ := he
        _ = _ := by rw [mul_left_comm, envelope_identity (hu x hx)]; rfl
    _ = Real.sqrt (5*C)*(ε*(∫x in Icc (0:ℝ) 1, (δ+x)^(-(3/2:ℝ)))+
        B*(∫x in Icc (0:ℝ) 1, (δ+x)^(-(1/2:ℝ)))) := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add (hi1.const_mul ε) (hi2.const_mul B),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (integral_inverse_cube hδ) hε)
      (mul_le_mul_of_nonneg_left (integral_inverse_sqrt hδ) hB)) (Real.sqrt_nonneg _)

lemma scaled_expression {δ d s e W ε B : ℝ} (hd : d≠0) (hδ : δ=d^2) :
    δ*(2*W*(s/d)+(s/d)*s*(ε*(2/d)+B*(2*e))) =
      2*W*s*d+2*s^2*ε+2*s^2*B*d*e := by
  rw [hδ]
  field_simp
  ring

lemma normalized_bound {C W δ ε B D : ℝ} (hC : 0≤C) (hW : 0≤W)
    (hδ : 0<δ) (hδ1 : δ≤1) (hε : 0≤ε) (hB : 0≤B)
    (hD : D ≤ 2*Real.sqrt W*Real.sqrt (C*(2+1/δ)) +
      Real.sqrt (C*(2+1/δ))*Real.sqrt (5*C)*
        (ε*(2/Real.sqrt δ)+B*(2*Real.sqrt (δ+1)))) :
    δ*D ≤ 10*C*ε+(2*Real.sqrt W*Real.sqrt (5*C)+20*C*B)*Real.sqrt δ := by
  have hd : 0<Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hsqrtW : 0 ≤ Real.sqrt W := by
    simpa only [Real.sqrt_zero] using Real.sqrt_le_sqrt hW
  have hc := sqrt_energy_le hC hδ (hδ1.trans (by norm_num : (1:ℝ)≤2))
  rw [Real.rpow_neg hδ.le,←Real.sqrt_eq_rpow,←div_eq_mul_inv] at hc
  have hA : 0≤ε*(2/Real.sqrt δ)+B*(2*Real.sqrt (δ+1)) := by positivity
  have hle : D ≤ 2*Real.sqrt W*(Real.sqrt (5*C)/Real.sqrt δ)+
      (Real.sqrt (5*C)/Real.sqrt δ)*Real.sqrt (5*C)*
        (ε*(2/Real.sqrt δ)+B*(2*Real.sqrt (δ+1))) := by
    apply hD.trans
    exact add_le_add (mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num) hsqrtW))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) hA)
  have hs : (Real.sqrt (5*C))^2=5*C := Real.sq_sqrt (by positivity)
  have he : Real.sqrt (δ+1)≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by linarith⟩
  calc
    _ ≤ δ*(2*Real.sqrt W*(Real.sqrt (5*C)/Real.sqrt δ)+
      (Real.sqrt (5*C)/Real.sqrt δ)*Real.sqrt (5*C)*
        (ε*(2/Real.sqrt δ)+B*(2*Real.sqrt (δ+1)))) := mul_le_mul_of_nonneg_left hle hδ.le
    _ = 2*Real.sqrt W*Real.sqrt (5*C)*Real.sqrt δ+10*C*ε+
        10*C*B*Real.sqrt δ*Real.sqrt (δ+1) := by
      rw [scaled_expression hd.ne' (Real.sq_sqrt hδ.le).symm,hs]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left he (show 0≤10*C*B*Real.sqrt δ by positivity)
      nlinarith

end OrdinaryHalaszEnvelopes

end

end OAI
