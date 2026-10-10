import OAI.NumberTheory.DirichletL.Hecke.DyadicScale
import OAI.NumberTheory.DirichletL.Hecke.DyadicTailBudget

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeDeletionBounds HeckeReciprocalGrowth HeckeLogarithmic

theorem presentation_cost (χ : Character) (U H ε : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hε : 0≤ε) (hε' : ε≤1) :
    (presentationComplexity χ H)^ε≤2*U^(2*ε)*(3+H)^2 := by
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have hbase : 1≤3+H := by linarith
  have hc := presentationComplexity_le_of_modulus_le χ U H hQ
  rw [abs_of_nonneg hH] at hc
  have hp : (presentationComplexity χ H)^ε≤(2*U^2*(3+H)^2)^ε :=
    Real.rpow_le_rpow (by unfold presentationComplexity complexity; positivity) hc hε
  have he : (2*U^2*(3+H)^2)^ε=(2 : ℝ)^ε*U^(2*ε)*(3+H)^(2*ε) := by
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by norm_num) (by positivity)]
    simp only [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤U),
      ←Real.rpow_mul (by linarith : 0≤3+H),Nat.cast_ofNat]
  rw [he] at hp
  have h2 : (2 : ℝ)^ε≤2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hε'
  have hh : (3+H)^(2*ε)≤(3+H)^2 := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num; linarith)
  exact hp.trans (mul_le_mul (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by linarith) _))
    hh (Real.rpow_nonneg (by linarith) _) (by positivity))

theorem positive_central_cost (χ : Character) (U H a e ε η r : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hε : 0≤ε) (hε' : ε≤1)
    (hheight : (3+H)^4≤U^η) :
    (U^r)^(a+6*e-1/2)*(presentationComplexity χ H)^ε≤
      2*U^((a-1/2+6*e)*r+2*ε+η) := by
  have hU : 0<U := lt_of_lt_of_le zero_lt_one ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hh : (3+H)^2≤U^η := by
    apply le_trans _ hheight
    exact pow_le_pow_right₀ (by linarith) (by decide : 2≤4)
  calc
    _ ≤ (U^r)^(a+6*e-1/2)*(2*U^(2*ε)*U^η) :=
      mul_le_mul_of_nonneg_left ((presentation_cost χ U H ε hQ hH hε hε').trans
        (mul_le_mul_of_nonneg_left hh (by positivity))) (by positivity)
    _ = _ := by
      rw [positive_scale_exponent U a e r hU]
      rw [Real.rpow_add hU,Real.rpow_add hU]
      ring

theorem reflected_central_cost (χ : Character) (U H a e ε η m : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (ha : 1/2≤a)
    (he : 0≤e) (hε : 0≤ε) (hε' : ε≤1) (hheight : (3+H)^4≤U^η) :
    (χ.modulus.absNorm : ℝ)^(a-1/2+6*e)*
      ((radical χ.modulus).absNorm : ℝ)^(6*e+2*ε)*(3+H)^2*
      (presentationComplexity χ H)^ε*(U^m)^(1/2-a-6*e)≤
      2*U^((a-1/2)*(1-m)+6*e*(2-m)+4*ε+η) := by
  have hU : 0<U := lt_of_lt_of_le zero_lt_one ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hcost := reflected_conductor_cost χ U a e ε hQ ha he hε
  have hcomplex := presentation_cost χ U H ε hQ hH hε hε'
  have hcomplex0 : 0≤(presentationComplexity χ H)^ε := Real.rpow_nonneg (by
    unfold presentationComplexity complexity
    positivity) _
  calc
    _ ≤ U^(a-1/2+12*e+2*ε)*(3+H)^2*(2*U^(2*ε)*(3+H)^2)*(U^m)^(1/2-a-6*e) := by
      gcongr
    _ = 2*(U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e))*U^(2*ε)*(3+H)^4 := by ring
    _ ≤ 2*(U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e))*U^(2*ε)*U^η :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    _ = _ := by
      rw [reflected_scale_exponent U a e ε m hU]
      calc
        _ = 2*(U^((a-1/2)*(1-m)+6*e*(2-m)+2*ε)*U^(2*ε)*U^η) := by ring
        _ = 2*U^(((a-1/2)*(1-m)+6*e*(2-m)+2*ε)+2*ε+η) := by
          rw [←Real.rpow_add hU,←Real.rpow_add hU]
        _ = _ := by congr 2; ring

theorem direct_external_cost (χ : Character) (U H κ η r R : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hκ : 0≤κ) (hκ' : κ≤1)
    (hr : 0≤r) (hrR : r≤R) (hheight : (3+H)^4≤U^η) :
    (U^r)^(3/2 : ℝ)*(presentationComplexity χ H)^κ≤2*U^(2*R+2+η) := by
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have h := positive_central_cost χ U H 2 0 κ η r hQ hH hκ hκ' hheight
  norm_num only [mul_zero,add_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le hU
  nlinarith

theorem reflected_external_cost (χ : Character) (U H κ η r R : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hκ : 0≤κ) (hκ' : κ≤1)
    (hr : 0≤r) (hrR : r≤R) (hheight : (3+H)^4≤U^η) :
    (U^r)^(3/2 : ℝ)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
      ((radical χ.modulus).absNorm : ℝ)^(1/10+κ)*(3+H)^2≤U^(2*R+2+η) := by
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hR := (radical_norm_le_modulus χ).trans hQ
  have hh : (3+H)^2≤U^η :=
    (pow_le_pow_right₀ (by linarith) (by decide : 2≤4)).trans hheight
  calc
    _ ≤ (U^r)^(3/2 : ℝ)*U^(3/5 : ℝ)*U^(1/10+κ)*U^η := by
      gcongr
    _ = U^(r*(3/2)+(3/5)+(1/10+κ)+η) := by
      rw [←Real.rpow_mul hUp.le,←Real.rpow_add hUp,←Real.rpow_add hUp,←Real.rpow_add hUp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)

end SevenEighths.HeckeDyadic

end

end OAI
