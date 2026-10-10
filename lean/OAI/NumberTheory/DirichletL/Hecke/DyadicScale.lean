import OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedPointwise

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeDeletionBounds HeckeReciprocalGrowth HeckeLogarithmic

theorem radical_dvd (M : Ideal O) (hM : M≠0) : radical M∣M := by
  unfold radical SmoothMobiusCorrection.primeProduct
  rw [SmoothMobiusCorrection.prod_primeSet M (fun J : Ideal O => J)]
  exact IdealMobiusDivisorSum.support_product_dvd hM (Finset.Subset.refl _)

theorem radical_norm_le_modulus (χ : Character) :
    ((radical χ.modulus).absNorm : ℝ)≤χ.modulus.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))
    (map_dvd Ideal.absNorm (radical_dvd χ.modulus χ.modulus_ne_bot))

theorem presentationComplexity_le_of_modulus_le (χ : Character) (U H : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) :
    presentationComplexity χ H≤2*U^2*(3+|H|)^2 := by
  have hR := (radical_norm_le_modulus χ).trans hQ
  have hU : 0≤U := (Nat.cast_nonneg χ.modulus.absNorm).trans hQ
  unfold presentationComplexity complexity
  calc
    _ ≤ U*(2*U*(3+|H|)^2) := by gcongr
    _ = _ := by ring

theorem reflected_conductor_cost (χ : Character) (U a e ε : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (ha : 1/2≤a) (he : 0≤e) (hε : 0≤ε) :
    (χ.modulus.absNorm : ℝ)^(a-1/2+6*e)*
      ((radical χ.modulus).absNorm : ℝ)^(6*e+2*ε)≤U^(a-1/2+12*e+2*ε) := by
  have hU : 0<U := lt_of_lt_of_le zero_lt_one
    ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hR := (radical_norm_le_modulus χ).trans hQ
  calc
    _ ≤ U^(a-1/2+6*e)*U^(6*e+2*ε) :=
      mul_le_mul (Real.rpow_le_rpow (by positivity) hQ (by linarith))
        (Real.rpow_le_rpow (by positivity) hR (by positivity))
        (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hU.le _)
    _ = _ := by
      rw [←Real.rpow_add hU]
      congr 1
      ring

theorem positive_scale_exponent (U a e r : ℝ) (hU : 0<U) :
    (U^r)^(a+6*e-1/2)=U^((a-1/2+6*e)*r) := by
  rw [←Real.rpow_mul hU.le]
  congr 1
  ring

theorem reflected_scale_exponent (U a e ε m : ℝ) (hU : 0<U) :
    U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e)=
      U^((a-1/2)*(1-m)+6*e*(2-m)+2*ε) := by
  rw [←Real.rpow_mul hU.le,←Real.rpow_add hU]
  congr 1
  ring

end SevenEighths.HeckeDyadic

end

end OAI
