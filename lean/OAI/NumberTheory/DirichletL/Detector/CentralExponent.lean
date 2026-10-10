import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeCentralExponent

def sourceExponent (a d R q : ℝ) : ℝ :=
  (17/48)*(1/2-17/50)+a+17/50-1-a*(23/48)-d*(17/50)+d*R+
    d*(a-1/2)+(1/6)*(17/50-1/2+q)

def relativeExponent (δ d R q : ℝ) : ℝ :=
  -1/48+(2/3)*δ+q/6-(13/16)*(1-R)+(d-13/16)*(R+δ/2-17/50)

lemma original_exponent_identity (a d R q : ℝ) :
    sourceExponent a d R q=3/16+relativeExponent (2*a-1) d R q := by
  unfold sourceExponent relativeExponent
  ring

lemma frequency_slope_bounds (δ R : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤1)
    (hRlo : 1-δ≤R) (hRhi : R≤139/96) :
    4/25≤R+δ/2-17/50 ∧ R+δ/2-17/50≤2 := by
  constructor <;> linarith

lemma relative_extend (δ d R q ζ : ℝ) (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    relativeExponent δ d R q≤relativeExponent δ (13/16) R q+2*ζ := by
  have hh := mul_le_mul_of_nonneg_right (show d-13/16≤ζ by linarith) hslo
  have hh' := mul_le_mul_of_nonneg_left hshi hζ
  unfold relativeExponent
  nlinarith

lemma balanced_source_margin (δ x R Δ loss ζ d : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤5/6) (hx : 0≤x) (hx1 : x≤1/2)
    (hR : R≤Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    sourceExponent ((1+δ)/2) d R (δ*x)-(3/16+Δ)≤
      -49/440640-(51/64)*Δ+(13/16)*loss+2*ζ := by
  have hb := Endpoint.balanced_endpoint_margin hδ hδ1
    (show 0≤1/2-x by linarith) (show 1/2-x≤1/2 by linarith)
  have he := relative_extend δ d R (δ*x) ζ hζ hd hslo hshi
  rw [original_exponent_identity]
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid]
  unfold Endpoint.balancedExponent at hb
  unfold relativeExponent at he ⊢
  nlinarith

lemma high_source_margin (δ R q Δ loss ζ d : ℝ)
    (hq : q≤δ/2) (hR : R≤1-δ+loss)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    sourceExponent ((1+δ)/2) d R q-(3/16+Δ)≤
      -1/48-δ/16-Δ+(13/16)*loss+2*ζ := by
  have he := relative_extend δ d R q ζ hζ hd hslo hshi
  rw [original_exponent_identity]
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid]
  unfold relativeExponent at he ⊢
  nlinarith

lemma floor_source_margin (q Δ ζ d : ℝ) (hq : q≤1/100)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ) :
    sourceExponent (51/100) d 1 q-(3/16+Δ)≤-7/1200-Δ+2*ζ := by
  have he := relative_extend (1/50) d 1 q ζ hζ hd (by norm_num) (by norm_num)
  rw [original_exponent_identity]
  norm_num only at *
  unfold relativeExponent at he ⊢
  nlinarith

lemma intermediate_source_margin (δ q Δ d : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤5/6)
    (hq : q≤δ/2) (hd : d≤1/2) :
    sourceExponent ((1+δ)/2) d (76/75-(2/3)*δ) q-(3/16+Δ)≤-49/14400-Δ := by
  have hs : 0≤(76/75-(2/3)*δ)+δ/2-17/50 := by linarith
  have hm := mul_le_mul_of_nonneg_right hd hs
  unfold sourceExponent
  nlinarith

def realLoss (N : ℕ) (d e eps heightLoss mesh : ℝ) : ℝ :=
  (105/8)*e+12*d*e+d*eps*(N+8)+heightLoss+mesh/6

lemma realLoss_bound (N : ℕ) (d e eps heightLoss mesh : ℝ)
    (hd : d≤1) (he : 0≤e) (heps : 0≤eps) :
    realLoss N d e eps heightLoss mesh≤26*e+(N+8)*eps+heightLoss+mesh/6 := by
  have h1 := mul_le_mul_of_nonneg_right hd he
  have h2 := mul_le_mul_of_nonneg_right hd (show 0≤eps*(N+8) by positivity)
  unfold realLoss
  nlinarith

lemma physical_scale_identity (Z a e : ℝ) (hZ : 0<Z) :
    (Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e)=
      Z^((25/48)*a-181/300+(105/8)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring
end SevenEighths.ProbeCentralExponent

end

end OAI
