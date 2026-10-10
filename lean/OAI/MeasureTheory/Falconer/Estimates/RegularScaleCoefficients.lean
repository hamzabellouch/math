import OAI.MeasureTheory.Falconer.Estimates.TwoScaleRatio

namespace OAI

/-! Polynomial bounds for the two factors in the regular-cell scale
comparison. The exponents leave room for the finite selection losses. -/
namespace Falconer

theorem regular_local_coefficient_bound {D Δ s p : ℝ}
    (hD : 80 ≤ D) (hΔ : 0 < Δ) (_hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hp : 0 ≤ p) (hpD : p ≤ D) :
    ((D*3^s)*(80*Δ)^s*(D/(Δ^s)^2))*(1+(D*3^s)*p) ≤ D^8/Δ^s := by
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have h3 : (3:ℝ)^s ≤ D := by
    apply le_trans _ (show (3:ℝ) ≤ D by linarith only [hD])
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
  have h80 : (80:ℝ)^s ≤ D := by
    apply le_trans _ hD
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
  have hpterm : 1+(D*3^s)*p ≤ D^4 := by
    calc
      _ ≤ 1+(D*D)*D := by gcongr
      _ = 1+D^3 := by ring
      _ ≤ D^4 := by
        have hh : 2 ≤ D := by linarith only [hD]
        have hpow := one_le_pow₀ hD1 (n := 3)
        nlinarith only [mul_le_mul_of_nonneg_right hh (pow_nonneg hD0 3),hpow]
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hΔ.le]
  calc
    _ ≤ ((D*D)*(D*Δ^s)*(D/(Δ^s)^2))*D^4 := by gcongr
    _ = _ := by field_simp

theorem regular_coarse_coefficient_bound {D s p β : ℝ}
    (hD : 80 ≤ D) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hp : 0 ≤ p) (hpD : p ≤ D) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    D^2*(D^2*80^s)^(1-β)*(25921:ℝ)^β*(1+D*p) ≤ D^11 := by
  have hD1 : 1 ≤ D := by linarith only [hD]
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have h80 : (80:ℝ)^s ≤ D := by
    apply le_trans _ hD
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
  have hbase : 1 ≤ D^2*80^s := by
    have hpow : 1 ≤ (80:ℝ)^s := Real.one_le_rpow (by norm_num) hs
    nlinarith only [one_le_pow₀ hD1 (n := 2),hpow]
  have hfirst : (D^2*80^s)^(1-β) ≤ D^3 := by
    calc
      _ ≤ D^2*80^s := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (y := 1-β) (z := 1) hbase (by linarith only [hβ])
      _ ≤ D^2*D := mul_le_mul_of_nonneg_left h80 (sq_nonneg D)
      _ = _ := by ring
  have hsecond : (25921:ℝ)^β ≤ D^3 := by
    calc
      (25921:ℝ)^β ≤ (25921:ℝ) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 25921) hβ1
      _ ≤ 80^3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hD 3
  have hlast : 1+D*p ≤ D^3 := by
    have hpow := one_le_pow₀ hD1 (n := 2)
    have hh : 2 ≤ D := by linarith only [hD]
    have hp2 : D*p ≤ D^2 := by nlinarith only [mul_le_mul_of_nonneg_left hpD hD0]
    nlinarith only [hp2,hpow,mul_le_mul_of_nonneg_right hh (sq_nonneg D)]
  calc
    _ ≤ D^2*D^3*D^3*D^3 := by gcongr
    _ = _ := by ring

theorem regular_local_ratio_bound {D Δ ρ s p A U m : ℝ}
    (hD : 80 ≤ D) (hΔ : 0 < Δ) (hρ : 0 < ρ) (hρΔ : ρ ≤ Δ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hp : 0 ≤ p) (hpD : p ≤ D)
    (hU : 0 ≤ U) (hm : 0 ≤ m) (hsmall : U ≤ D/(Δ^s)^4)
    (hproduct : (1/(D*(Δ^s)^2))^2*A ≤ 26*U*(D*m)*
      (((D*3^s)*(80*Δ)^s*(D/(Δ^s)^2))*(1+(D*3^s)*p))) :
    A*(ρ^s)^2 ≤ D^13*(m*ρ^s) := by
  have hD0 : 0 < D := by linarith only [hD]
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have hρs : 0 < ρ^s := Real.rpow_pos_of_pos hρ _
  have hscale : ρ^s ≤ Δ^s := Real.rpow_le_rpow hρ.le hρΔ hs
  have hcoeff := regular_local_coefficient_bound hD hΔ hs hs1 hp hpD
  have hraw : (1/(D*(Δ^s)^2))^2*A ≤ D^11*m/(Δ^s)^5 := by
    calc
      _ ≤ _ := hproduct
      _ ≤ D*U*(D*m)*(D^8/Δ^s) := by gcongr; linarith only [hD]
      _ ≤ D*(D/(Δ^s)^4)*(D*m)*(D^8/Δ^s) := by gcongr
      _ = _ := by field_simp
  have hh := mul_le_mul_of_nonneg_right hraw (sq_nonneg (D*(Δ^s)^2))
  have hA : A ≤ D^13*m/Δ^s := by
    convert hh using 1 <;> field_simp
  calc
    A*(ρ^s)^2 ≤ (D^13*m/Δ^s)*(ρ^s)^2 := mul_le_mul_of_nonneg_right hA (sq_nonneg _)
    _ = (D^13*m*ρ^s)*(ρ^s/Δ^s) := by ring
    _ ≤ (D^13*m*ρ^s)*1 := mul_le_mul_of_nonneg_left
      ((div_le_one hΔs).2 hscale) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
