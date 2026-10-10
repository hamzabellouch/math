import OAI.NumberTheory.DirichletL.Hecke.DetectorPrimeFamily

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRelativePrime
open HeckeFamily HeckeDetectorPrimeFamily

theorem idealCoeff_ne_zero_of_coprime (ν : Character) (J : Ideal O)
    (hJ : J≠0) (hc : IsCoprime J ν.modulus) : idealCoeff ν J≠0 := by
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν hg]
  apply MulChar.apply_ne_zero_iff.mpr
  apply (IdealCharacter.isUnit_mk_iff_isCoprime ν.modulus _).mpr
  simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hc

theorem idealCoeff_inverse (ν : Character) (J : Ideal O) :
    idealCoeff ν.inverse J=(idealCoeff ν J)⁻¹ := by
  by_cases hJ : J=0
  · subst J
    simp only [map_zero,inv_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν.inverse hg,
    idealCoeff_span ν hg,HeckeFamily.elementCoeff_inverse]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem relative_coefficient_on_ray (ν χ : Character) (hM : M≤ν.modulus)
    (J : Ideal O) (hJ : J∈RayQuotient.identityClass M H) :
    idealCoeff ((ν.product χ).product ν.inverse) J=idealCoeff χ J := by
  have hn := idealCoeff_ne_zero_of_coprime ν J hJ.1
    (HeckePrimeRow.identityClass_coprime_larger M H hJ hM)
  rw [idealCoeff_product,idealCoeff_product,idealCoeff_inverse]
  field_simp

theorem physical_eq_relative_average (data : RowData M) (ν : Character)
    (hM : M≤ν.modulus) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H data.u W b D z=
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H,
          HeckePrimeAnnular.primePolynomial
            ((ν.product (data.character M)).product
              (ν.inverse.product (HeckeRayQuotient.character M H hH θ)))
            W b D (1-z.re) z.im := by
  rw [data.amplitude_eq M H hH]
  have he : HeckePrimeRay.rayPrimePolynomial M H (data.character M) W b D (1-z.re) z.im=
      HeckePrimeRay.rayPrimePolynomial M H ((ν.product (data.character M)).product ν.inverse)
        W b D (1-z.re) z.im := by
    unfold HeckePrimeRay.rayPrimePolynomial
    congr 1
    apply Finset.sum_congr rfl
    intro J hJ
    rw [relative_coefficient_on_ray M H ν (data.character M) hM J (Finset.mem_filter.mp hJ).2.2]
  rw [he,HeckePrimeRay.rayPrimePolynomial_eq_average M H hH]
  congr 1
  apply Finset.sum_congr rfl
  intro θ hθ
  unfold HeckePrimeAnnular.primePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [HeckePrimeRay.twistedFamily,idealCoeff_product]
  ring

end SevenEighths.HeckeDetectorRelativePrime

end

end OAI
