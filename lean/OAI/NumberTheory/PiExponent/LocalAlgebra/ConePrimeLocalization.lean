import Mathlib.RingTheory.LocalRing.RingHom.Basic
import OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

def awayChartPrime : Ideal (ConeAway k σ) :=
  (laurentPrime (AffineRing k σ) P).comap (coneLaurentEquiv k σ).toRingHom

instance awayChartPrime_isPrime : (awayChartPrime k σ P).IsPrime := by
  unfold awayChartPrime
  infer_instance

def conePrime : Ideal (ConeRing k σ) :=
  (awayChartPrime k σ P).comap (algebraMap (ConeRing k σ) (ConeAway k σ))

instance conePrime_isPrime : (conePrime k σ P).IsPrime := by
  unfold conePrime
  infer_instance

theorem homogenizing_coordinate_not_mem_conePrime :
    (MvPolynomial.X none : ConeRing k σ) ∉ conePrime k σ P := by
  intro h
  change algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X none) ∈
    awayChartPrime k σ P at h
  exact (show (awayChartPrime k σ P).IsPrime from inferInstance).ne_top
    ((awayChartPrime k σ P).eq_top_of_isUnit_mem h
      (IsLocalization.Away.algebraMap_isUnit (S := ConeAway k σ)
        (MvPolynomial.X none : ConeRing k σ)))

def conePrimeLocalizationEquiv :
    Localization.AtPrime (conePrime k σ P) ≃+*
      Localization.AtPrime (laurentPrime (AffineRing k σ) P) :=
  (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ))
    (awayChartPrime k σ P)).toRingEquiv.trans
      (PiExponentJets.W22.primeLocalizationEquiv (coneLaurentEquiv k σ)
        (awayChartPrime k σ P) (laurentPrime (AffineRing k σ) P) rfl)

def affineLocalToConeLocal : Localization.AtPrime P →+*
    Localization.AtPrime (conePrime k σ P) :=
  (conePrimeLocalizationEquiv k σ P).symm.toRingHom.comp
    (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)))

@[instance_reducible] def affineLocalConeAlgebra :
    Algebra (Localization.AtPrime P) (Localization.AtPrime (conePrime k σ P)) :=
  (affineLocalToConeLocal k σ P).toAlgebra

theorem affineLocalToConeLocal_map_maximalIdeal :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (affineLocalToConeLocal k σ P) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (conePrime k σ P)) := by
  rw [affineLocalToConeLocal, ← Ideal.map_map,
    laurentLocal_maximalIdeal_map_eq (AffineRing k σ) P]
  exact IsLocalRing.map_maximalIdeal_of_surjective
    (conePrimeLocalizationEquiv k σ P).symm.toRingHom
    (conePrimeLocalizationEquiv k σ P).symm.surjective

theorem affineLocalToConeLocal_flat :
    letI := affineLocalConeAlgebra k σ P
    Module.Flat (Localization.AtPrime P) (Localization.AtPrime (conePrime k σ P)) := by
  let := affineLocalConeAlgebra k σ P
  let e : Localization.AtPrime (conePrime k σ P) ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime (laurentPrime (AffineRing k σ) P) :=
    { conePrimeLocalizationEquiv k σ P with
      commutes' := by
        intro a
        change conePrimeLocalizationEquiv k σ P
          ((conePrimeLocalizationEquiv k σ P).symm (algebraMap _ _ a)) = _
        exact (conePrimeLocalizationEquiv k σ P).apply_symm_apply _ }
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

theorem coneLocal_quotient_length
    (I : Ideal (Localization.AtPrime P))
    (hI : IsFiniteLength (Localization.AtPrime P) (Localization.AtPrime P ⧸ I)) :
    Module.length (Localization.AtPrime (conePrime k σ P))
      (Localization.AtPrime (conePrime k σ P) ⧸ I.map (affineLocalToConeLocal k σ P)) =
    Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ I) := by
  let := affineLocalConeAlgebra k σ P
  let := affineLocalToConeLocal_flat k σ P
  exact PiExponentJets.W25.length_quotient_map_of_flat_local
    (affineLocalToConeLocal_map_maximalIdeal k σ P) I hI

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
