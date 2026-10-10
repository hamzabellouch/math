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
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryRoughTarget
open Real
lemma exponent_budget {B : ℝ} (hB : 1≤B) :
    B^(-199979/50000:ℝ)/(B^(-10001/10000:ℝ))^4 *
      B^(-199979/200000:ℝ)*B^(-1/950:ℝ) ≤ B^(-10001/10000:ℝ) := by
  have hBp : 0<B := by linarith
  have he : (B^(-10001/10000:ℝ))^4 = B^(-10001/2500:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hBp.le];norm_num
  rw [he,div_eq_mul_inv,←Real.rpow_neg hBp.le,
    ←Real.rpow_add hBp,←Real.rpow_add hBp,←Real.rpow_add hBp]
  exact Real.rpow_le_rpow_of_exponent_le hB (by norm_num)

lemma numeric_budget {B d a u M e C₁ C₄ : ℝ}
    (hB : 1≤B) (hd : 0<d) (ha : 1≤a) (hu : 0≤u)
    (hM0 : 0≤M) (he0 : 0≤e) (hC₁ : 0<C₁) (hC₄ : 0<C₄)
    (hM : M≤C₁*B^(-199979/200000:ℝ))
    (he : e≤C₄*d^3*B^(-199979/50000:ℝ))
    (hbdy : 2*d*M≤B^(-10001/10000:ℝ)*u) :
    2*d*M+(u*B^(-10001/10000:ℝ)*(Real.sqrt d*Real.sqrt (a*d))+
      (e*d⁻¹^4)/(B^(-10001/10000:ℝ))^4*M*(a*d)*
        (8016*B^(-1/950:ℝ)*(a*d)*u))/d ≤
      (1+a+8016*C₄*C₁*a^2)*B^(-10001/10000:ℝ)*u := by
  have hBp : 0<B := by linarith
  have ha0 : 0≤a := by linarith
  have had : 0≤a*d := mul_nonneg ha0 hd.le
  have hsqrt : Real.sqrt d*Real.sqrt (a*d)≤a*d := by
    calc
      _ ≤ Real.sqrt (a*d)*Real.sqrt (a*d) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by nlinarith)) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt had
  have hlo : (u*B^(-10001/10000:ℝ)*(Real.sqrt d*Real.sqrt (a*d)))/d ≤
      a*B^(-10001/10000:ℝ)*u := by
    calc
      _ ≤ (u*B^(-10001/10000:ℝ)*(a*d))/d := by gcongr
      _ = _ := by field_simp
  have hhi : ((e*d⁻¹^4)/(B^(-10001/10000:ℝ))^4*M*(a*d)*
      (8016*B^(-1/950:ℝ)*(a*d)*u))/d ≤
      (8016*C₄*C₁*a^2)*B^(-10001/10000:ℝ)*u := by
    calc
      _ ≤ (((C₄*d^3*B^(-199979/50000:ℝ))*d⁻¹^4)/(B^(-10001/10000:ℝ))^4*
          (C₁*B^(-199979/200000:ℝ))*(a*d)*(8016*B^(-1/950:ℝ)*(a*d)*u))/d := by
        apply div_le_div_of_nonneg_right _ hd.le
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ had
        calc
          _ ≤ (e*d⁻¹^4)/(B^(-10001/10000:ℝ))^4*(C₁*B^(-199979/200000:ℝ)) :=
            mul_le_mul_of_nonneg_left hM
              (div_nonneg (mul_nonneg he0 (by positivity)) (by positivity))
          _ ≤ _ := mul_le_mul_of_nonneg_right ?_ (hM0.trans hM)
        gcongr
      _ = (8016*C₄*C₁*a^2)*(B^(-199979/50000:ℝ)/(B^(-10001/10000:ℝ))^4 *
          B^(-199979/200000:ℝ)*B^(-1/950:ℝ))*u := by
        field_simp
      _ ≤ _ := by gcongr;exact exponent_budget hB
  rw [add_div]
  nlinarith only [hbdy,hlo,hhi]
end OrdinaryRoughTarget

end

end OAI
