import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ContinuousOnShiftRpow

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set

namespace OrdinaryHalaszEnvelopes
open MeasureTheory Set

lemma integral_inverse_five_quarters {δ : ℝ} (hδ : 0<δ) :
    (∫x in Icc (0:ℝ) 1, (δ+x)^(-(5/4:ℝ))) ≤ 4*δ^(-(1/4:ℝ)) := by
  rw [integral_shift_rpow hδ (by norm_num)]
  norm_num
  nlinarith [Real.rpow_nonneg (show 0≤δ+1 by linarith) (-(1/4:ℝ))]

lemma band_envelope_identity {u ε B : ℝ} (hu : 0<u) :
    (ε/u+3*B*u^(-(3/4:ℝ)))*u^(-(1/2:ℝ)) =
      ε*u^(-(3/2:ℝ))+3*B*u^(-(5/4:ℝ)) := by
  rw [add_mul]
  congr 1
  · rw [div_eq_mul_inv,mul_assoc,←Real.rpow_neg_one u,←Real.rpow_add hu]
    norm_num
  · rw [mul_assoc,←Real.rpow_add hu]
    norm_num

lemma band_envelope_integral {C δ ε B : ℝ} (hC : 0≤C) (hδ : 0<δ)
    (hδ1 : δ≤1) (hε : 0≤ε) (hB : 0≤B) :
    (∫x in Icc (0:ℝ) 1, (ε/(δ+x)+3*B*(δ+x)^(-(3/4:ℝ)))*
      Real.sqrt (C*(2+1/(δ+x)))) ≤
      Real.sqrt (5*C)*(ε*(2/Real.sqrt δ)+12*B*δ^(-(1/4:ℝ))) := by
  have hu (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : 0<δ+x := by linarith [hx.1]
  have hi1 := (continuousOn_shift_rpow (r:=-(3/2:ℝ)) hδ).integrableOn_Icc («μ» := volume)
  have hi2 := (continuousOn_shift_rpow (r:=-(5/4:ℝ)) hδ).integrableOn_Icc («μ» := volume)
  have hc : ContinuousOn (fun x : ℝ => (ε/(δ+x)+3*B*(δ+x)^(-(3/4:ℝ)))*
      Real.sqrt (C*(2+1/(δ+x)))) (Icc 0 1) := by
    apply ContinuousOn.mul
    · exact (continuousOn_const.div (continuousOn_const.add continuousOn_id)
        (fun x hx => (hu x hx).ne')).add
        (continuousOn_const.mul (continuousOn_shift_rpow hδ))
    · apply ContinuousOn.sqrt
      exact continuousOn_const.mul (continuousOn_const.add (continuousOn_const.div
        (continuousOn_const.add continuousOn_id) (fun x hx => (hu x hx).ne')))
  calc
    _ ≤ ∫x in Icc (0:ℝ) 1, Real.sqrt (5*C)*(ε*(δ+x)^(-(3/2:ℝ))+
        3*B*(δ+x)^(-(5/4:ℝ))) := by
      apply integral_mono_ae hc.integrableOn_Icc
        (((hi1.const_mul ε).add (hi2.const_mul (3*B))).const_mul (Real.sqrt (5*C)))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have he := mul_le_mul_of_nonneg_left (sqrt_energy_le hC (hu x hx) (by linarith [hx.2]))
        (show 0≤ε/(δ+x)+3*B*(δ+x)^(-(3/4:ℝ)) by have hx0 := (hu x hx).le; positivity)
      calc
        _ ≤ _ := he
        _ = _ := by rw [mul_left_comm,band_envelope_identity (hu x hx)]; rfl
    _ = Real.sqrt (5*C)*(ε*(∫x in Icc (0:ℝ) 1, (δ+x)^(-(3/2:ℝ)))+
        3*B*(∫x in Icc (0:ℝ) 1, (δ+x)^(-(5/4:ℝ)))) := by
      rw [integral_const_mul,integral_add (hi1.const_mul ε) (hi2.const_mul (3*B)),
        integral_const_mul,integral_const_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      have h1 := mul_le_mul_of_nonneg_left (integral_inverse_cube hδ) hε
      have h2 := mul_le_mul_of_nonneg_left (integral_inverse_five_quarters hδ)
        (show 0≤3*B by positivity)
      nlinarith

lemma band_scale_identity {A δ : ℝ} (hA : 0<A) (hδ : 0<δ) :
    Real.sqrt δ*(A*δ)^(-(1/4:ℝ))*δ^(-(1/4:ℝ))=A^(-(1/4:ℝ)) := by
  rw [Real.mul_rpow hA.le hδ.le,Real.sqrt_eq_rpow]
  calc
    _ = A^(-(1/4:ℝ))*(δ^(1/2:ℝ)*δ^(-(1/4:ℝ))*δ^(-(1/4:ℝ))) := by ring
    _ = _ := by rw [←Real.rpow_add hδ,←Real.rpow_add hδ]; norm_num

lemma band_scaled_expression {δ d s w ε b z : ℝ} (hd : d≠0) (hδ : δ=d^2) :
    δ*(2*w*(s/d)+(s/d)*s*(ε*(2/d)+12*b*z)) =
      2*w*s*d+2*s^2*ε+12*s^2*d*b*z := by
  rw [hδ]
  field_simp
  ring

lemma band_normalized_bound {C W A δ ε D : ℝ} (hC : 0≤C) (_hW : 0≤W)
    (hA : 0<A) (hδ : 0<δ) (hδ1 : δ≤1) (hε : 0≤ε)
    (hD : D ≤ 2*Real.sqrt W*Real.sqrt (C*(2+1/δ)) +
      Real.sqrt (C*(2+1/δ))*Real.sqrt (5*C)*
        (ε*(2/Real.sqrt δ)+12*(A*δ)^(-(1/4:ℝ))*δ^(-(1/4:ℝ)))) :
    δ*D ≤ 10*C*ε+60*C*A^(-(1/4:ℝ))+
      2*Real.sqrt W*Real.sqrt (5*C)*Real.sqrt δ := by
  have hd : 0<Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hc := sqrt_energy_le hC hδ (hδ1.trans (by norm_num : (1:ℝ)≤2))
  rw [Real.rpow_neg hδ.le,←Real.sqrt_eq_rpow,←div_eq_mul_inv] at hc
  have hterm : 0≤ε*(2/Real.sqrt δ)+12*(A*δ)^(-(1/4:ℝ))*δ^(-(1/4:ℝ)) := by positivity
  have hle := add_le_add
    (mul_le_mul_of_nonneg_left hc (show 0≤2*Real.sqrt W by positivity))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (5*C))) hterm)
  have hs : (Real.sqrt (5*C))^2=5*C := Real.sq_sqrt (by positivity)
  have hscale := band_scale_identity hA hδ
  calc
    δ*D ≤ δ*(2*Real.sqrt W*(Real.sqrt (5*C)/Real.sqrt δ)+
      (Real.sqrt (5*C)/Real.sqrt δ)*Real.sqrt (5*C)*
        (ε*(2/Real.sqrt δ)+12*(A*δ)^(-(1/4:ℝ))*δ^(-(1/4:ℝ)))) :=
      mul_le_mul_of_nonneg_left (hD.trans hle) hδ.le
    _ = 10*C*ε+60*C*(Real.sqrt δ*(A*δ)^(-(1/4:ℝ))*δ^(-(1/4:ℝ)))+
        2*Real.sqrt W*Real.sqrt (5*C)*Real.sqrt δ := by
      rw [band_scaled_expression hd.ne' (Real.sq_sqrt hδ.le).symm,hs]
      ring
    _ = _ := by rw [hscale]

end OrdinaryHalaszEnvelopes

end

end OAI
