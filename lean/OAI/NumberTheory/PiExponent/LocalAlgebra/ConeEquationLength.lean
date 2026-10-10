import OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations

namespace OAI

noncomputable section

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

namespace PiExponentSiegel.W17.ConeLocalLength

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem conePrimeLocalizationEquiv_algebraMap (F : ConeRing k σ) :
    conePrimeLocalizationEquiv k σ P
      (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)) F) =
    algebraMap (LaurentChart k σ)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) (coneToLaurent k σ F) := by
  let a := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ)) (awayChartPrime k σ P)
  let b := PiExponentJets.W22.primeLocalizationEquiv (coneLaurentEquiv k σ)
    (awayChartPrime k σ P) (laurentPrime (AffineRing k σ) P) rfl
  change b (a (algebraMap (ConeRing k σ) _ F)) = _
  rw [a.commutes F]
  change b (algebraMap (ConeAway k σ) _ (algebraMap (ConeRing k σ) (ConeAway k σ) F)) = _
  rw [show b (algebraMap (ConeAway k σ) _
      (algebraMap (ConeRing k σ) (ConeAway k σ) F)) =
      algebraMap (LaurentChart k σ) _ ((coneLaurentEquiv k σ)
        (algebraMap (ConeRing k σ) (ConeAway k σ) F)) from
    IsLocalization.ringEquivOfRingEquiv_eq
      (PiExponentJets.W22.primeCompl_map_eq_of_comap (coneLaurentEquiv k σ)
        (awayChartPrime k σ P) (laurentPrime (AffineRing k σ) P) rfl) _]
  exact congrArg (algebraMap (LaurentChart k σ)
    (Localization.AtPrime (laurentPrime (AffineRing k σ) P)))
    (coneAwayToLaurent_algebraMap k σ F)

theorem conePrimeLocalizationEquiv_map_ideal (J : Ideal (ConeRing k σ)) :
    (J.map (algebraMap (ConeRing k σ)
      (Localization.AtPrime (conePrime k σ P)))).map
        (conePrimeLocalizationEquiv k σ P).toRingHom =
    (J.map (coneToLaurent k σ)).map (algebraMap (LaurentChart k σ)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro F
  exact conePrimeLocalizationEquiv_algebraMap k σ P F

theorem affine_ideal_map_to_laurent_local (J : Ideal (AffineRing k σ)) :
    (J.map (algebraMap (AffineRing k σ) (Localization.AtPrime P))).map
      (algebraMap (Localization.AtPrime P)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P))) =
    (J.map (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ)).map
      (algebraMap (LaurentChart k σ)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  rw [LaurentPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]

theorem homogenized_cone_local_length_eq {ι : Type*} (f : ι → AffineRing k σ)
    (hfinite : IsFiniteLength (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (AffineRing k σ) (Localization.AtPrime P)))) :
    Module.length (Localization.AtPrime (conePrime k σ P))
      (Localization.AtPrime (conePrime k σ P) ⧸
        (Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))).map
          (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)))) =
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (AffineRing k σ) (Localization.AtPrime P))) := by
  let J := Ideal.span (Set.range f)
  let H := Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))
  have hid := conePrimeLocalizationEquiv_map_ideal k σ P H
  rw [map_homogenized_span_eq_laurent_span k σ f] at hid
  have hlength := PiExponentJets.W22.quotient_length_eq_of_ringEquiv
    (conePrimeLocalizationEquiv k σ P)
    (H.map (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))))
    ((J.map (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ)).map
      (algebraMap (LaurentChart k σ)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P)))) hid.symm
  apply hlength.trans
  have h := laurentLocal_quotient_length (AffineRing k σ) P
    (J.map (algebraMap (AffineRing k σ) (Localization.AtPrime P))) hfinite
  rw [affine_ideal_map_to_laurent_local k σ P J] at h
  exact h

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
