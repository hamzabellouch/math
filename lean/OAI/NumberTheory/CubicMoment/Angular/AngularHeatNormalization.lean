import OAI.NumberTheory.CubicMoment.Angular.AngularHeatFactor
import OAI.NumberTheory.CubicMoment.Estimates.ResidueHarmonicTransform

namespace OAI

/-! Exact normalization of the angular polynomial theta transformation. -/
noncomputable section
namespace CubicFirstMoment

lemma heat_radial_normalization {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (n : ℕ) :
    (1/t/A)^((n:ℝ)/2)*t^n = (t/A)^((n:ℝ)/2) := by
  have hp : t^n = (t^2)^((n:ℝ)/2) := by
    rw [←Real.rpow_natCast t 2,←Real.rpow_mul ht.le]
    have he : (2:ℝ)*((n:ℝ)/2) = n := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he,Real.rpow_natCast]
  rw [hp,←Real.mul_rpow (by positivity : 0 ≤ 1/t/A) (sq_nonneg t)]
  congr 1
  field_simp

lemma angularHeat_nat_transformation {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (G : ℂ)
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h))
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    angularLatticeHeat q χ (n:ℤ) (residueHeckeScale q) ((n:ℝ)/2) (1/t) =
      ((G/(Real.sqrt (norm q):ℝ))*(angularConductorPhase q)^n)*(t:ℂ)*
        angularLatticeHeat q (star χ) (-(n:ℤ)) (residueHeckeScale q) ((n:ℝ)/2) t := by
  have hA := residueHeckeScale_pos hq
  rw [angularHeat_nat_factor q χ hA (one_div_pos.mpr ht),
    residueHarmonic_transform hq χ G hFourier (one_div_pos.mpr ht),
    angularHeat_neg_nat_factor q (star χ) hA ht,one_div_one_div]
  have hp : (angularConductorPhase q/((1/t:ℝ):ℂ))^n =
      (angularConductorPhase q)^n*(t:ℂ)^n := by
    rw [Complex.ofReal_div,Complex.ofReal_one,div_div_eq_mul_div,div_one,mul_pow]
  rw [hp]
  have hr : (((1/t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ)*(t:ℂ)^n =
      (((t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ) := by
    exact_mod_cast heat_radial_normalization hA ht n
  have htC := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  calc
    _ = (G/(Real.sqrt (norm q):ℝ))*(angularConductorPhase q)^n*(t:ℂ)*
        ((((1/t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ)*(t:ℂ)^n)*
        residueAntiHarmonicTheta q (star χ) (residueHeckeScale q) n t := by
      field_simp
    _ = _ := by rw [hr]; ring

lemma angularHeat_neg_nat_transformation {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (G : ℂ)
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h))
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    angularLatticeHeat q χ (-(n:ℤ)) (residueHeckeScale q) ((n:ℝ)/2) (1/t) =
      ((G/(Real.sqrt (norm q):ℝ))*(angularConductorPhaseNeg q)^n)*(t:ℂ)*
        angularLatticeHeat q (star χ) (n:ℤ) (residueHeckeScale q) ((n:ℝ)/2) t := by
  have hA := residueHeckeScale_pos hq
  rw [angularHeat_neg_nat_factor q χ hA (one_div_pos.mpr ht),
    residueAntiHarmonic_transform hq χ G hFourier (one_div_pos.mpr ht),
    angularHeat_nat_factor q (star χ) hA ht,one_div_one_div]
  have hp : (angularConductorPhaseNeg q/((1/t:ℝ):ℂ))^n =
      (angularConductorPhaseNeg q)^n*(t:ℂ)^n := by
    rw [Complex.ofReal_div,Complex.ofReal_one,div_div_eq_mul_div,div_one,mul_pow]
  rw [hp]
  have hr : (((1/t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ)*(t:ℂ)^n =
      (((t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ) := by
    exact_mod_cast heat_radial_normalization hA ht n
  have htC := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  calc
    _ = (G/(Real.sqrt (norm q):ℝ))*(angularConductorPhaseNeg q)^n*(t:ℂ)*
        ((((1/t/residueHeckeScale q)^((n:ℝ)/2):ℝ):ℂ)*(t:ℂ)^n)*
        residueHarmonicTheta q (star χ) (residueHeckeScale q) n t := by
      field_simp
    _ = _ := by rw [hr]; ring

end CubicFirstMoment

end

end OAI
