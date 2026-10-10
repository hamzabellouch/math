import OAI.NumberTheory.CubicMoment.Estimates.ResidueHarmonicPoisson
import OAI.NumberTheory.CubicMoment.Angular.AngularConductorPhase

namespace OAI

/-! The polynomial Gaussian theta transformation before the final
normalization by the angular radial weight. -/
noncomputable section
namespace CubicFirstMoment

lemma residueHarmonic_transform {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (G : ℂ)
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h))
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    residueHarmonicTheta q χ (residueHeckeScale q) n t =
      (1/(Real.sqrt (norm q)*t):ℝ)*G*(angularConductorPhase q/(t:ℂ))^n*
        residueAntiHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t) := by
  have hA := residueHeckeScale_pos hq
  rw [residueHarmonic_poisson hq χ hA ht]
  simp_rw [residueGaussian_exponent hq ht,hFourier]
  have hf (h : Eisenstein) :
      (G*(star χ) (Ideal.Quotient.mk (modulus q) h))*
        ((-2*(Real.pi:ℂ)*Complex.I/(t/residueHeckeScale q:ℝ))^n*
          (star ((h:ℂ)/((q:ℂ)*traceLambda)))^n*(Real.pi/(t/residueHeckeScale q):ℝ)*
          (Real.exp (-norm h/(residueHeckeScale q*t)):ℝ)) =
      (Real.pi/(t/residueHeckeScale q):ℝ)*G*(angularConductorPhase q/(t:ℂ))^n*
        ((star χ) (Ideal.Quotient.mk (modulus q) h)*
          ((star (h:ℂ))^n*(Real.exp (-norm h*(1/t)/residueHeckeScale q):ℝ))) := by
    have hexp : -norm h/(residueHeckeScale q*t) = -norm h*(1/t)/residueHeckeScale q := by ring
    rw [hexp,star_div₀]
    have hpoly : (-2*(Real.pi:ℂ)*Complex.I/(t/residueHeckeScale q:ℝ))*
        (star (h:ℂ)/star ((q:ℂ)*traceLambda)) =
      (angularConductorPhase q/(t:ℂ))*star (h:ℂ) := by
      unfold angularConductorPhase
      push_cast
      field_simp
    rw [←mul_pow,hpoly,mul_pow]
    ring
  simp_rw [hf]
  rw [tsum_mul_left]
  change ((2/(Real.sqrt 3*norm q):ℝ):ℂ)*
    (((Real.pi/(t/residueHeckeScale q):ℝ):ℂ)*G*(angularConductorPhase q/(t:ℂ))^n*
      residueAntiHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t)) = _
  rw [show ((2/(Real.sqrt 3*norm q):ℝ):ℂ)*
      (((Real.pi/(t/residueHeckeScale q):ℝ):ℂ)*G*(angularConductorPhase q/(t:ℂ))^n*
        residueAntiHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t)) =
      (((2/(Real.sqrt 3*norm q))*(Real.pi/(t/residueHeckeScale q)):ℝ):ℂ)*G*
        (angularConductorPhase q/(t:ℂ))^n*
          residueAntiHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t) by push_cast; ring]
  rw [residueGaussian_prefactor hq ht]

lemma residueAntiHarmonic_transform {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (G : ℂ)
    (hFourier : ∀ h : Eisenstein, residueFiniteFourier q χ h =
      G*(star χ) (Ideal.Quotient.mk (modulus q) h))
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    residueAntiHarmonicTheta q χ (residueHeckeScale q) n t =
      (1/(Real.sqrt (norm q)*t):ℝ)*G*(angularConductorPhaseNeg q/(t:ℂ))^n*
        residueHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t) := by
  have hA := residueHeckeScale_pos hq
  rw [residueAntiHarmonic_poisson hq χ hA ht]
  simp_rw [residueGaussian_exponent hq ht,hFourier]
  have hf (h : Eisenstein) :
      (G*(star χ) (Ideal.Quotient.mk (modulus q) h))*
        ((-2*(Real.pi:ℂ)*Complex.I/(t/residueHeckeScale q:ℝ))^n*
          ((h:ℂ)/((q:ℂ)*traceLambda))^n*(Real.pi/(t/residueHeckeScale q):ℝ)*
          (Real.exp (-norm h/(residueHeckeScale q*t)):ℝ)) =
      (Real.pi/(t/residueHeckeScale q):ℝ)*G*(angularConductorPhaseNeg q/(t:ℂ))^n*
        ((star χ) (Ideal.Quotient.mk (modulus q) h)*
          ((h:ℂ)^n*(Real.exp (-norm h*(1/t)/residueHeckeScale q):ℝ))) := by
    have hexp : -norm h/(residueHeckeScale q*t) = -norm h*(1/t)/residueHeckeScale q := by ring
    rw [hexp]
    have hpoly : (-2*(Real.pi:ℂ)*Complex.I/(t/residueHeckeScale q:ℝ))*
        ((h:ℂ)/((q:ℂ)*traceLambda)) =
      (angularConductorPhaseNeg q/(t:ℂ))*(h:ℂ) := by
      unfold angularConductorPhaseNeg
      push_cast
      field_simp
    rw [←mul_pow,hpoly,mul_pow]
    ring
  simp_rw [hf]
  rw [tsum_mul_left]
  change ((2/(Real.sqrt 3*norm q):ℝ):ℂ)*
    (((Real.pi/(t/residueHeckeScale q):ℝ):ℂ)*G*(angularConductorPhaseNeg q/(t:ℂ))^n*
      residueHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t)) = _
  rw [show ((2/(Real.sqrt 3*norm q):ℝ):ℂ)*
      (((Real.pi/(t/residueHeckeScale q):ℝ):ℂ)*G*(angularConductorPhaseNeg q/(t:ℂ))^n*
        residueHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t)) =
      (((2/(Real.sqrt 3*norm q))*(Real.pi/(t/residueHeckeScale q)):ℝ):ℂ)*G*
        (angularConductorPhaseNeg q/(t:ℂ))^n*
          residueHarmonicTheta q (star χ) (residueHeckeScale q) n (1/t) by push_cast; ring]
  rw [residueGaussian_prefactor hq ht]

end CubicFirstMoment

end

end OAI
