import Mathlib.RingTheory.LocalRing.Quotient
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionMinimalSum
import OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem quotient_cut_length (I J : Ideal A) :
    Module.length A (A ⧸ (I ⊔ J)) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) := by
  calc
    Module.length A (A ⧸ (I ⊔ J)) =
        Module.length (A ⧸ (I ⊔ J)) (A ⧸ (I ⊔ J)) :=
      PiExponentSiegel.W23.quotient_module_length_eq_intrinsic _
    _ = Module.length ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
        ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) :=
      (PiExponentSiegel.W23.intrinsic_length_eq_of_ringEquiv
        (DoubleQuot.quotQuotEquivQuotSup I J)).symm
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) :=
      (PiExponentSiegel.W23.quotient_module_length_eq_intrinsic _).symm

theorem quotient_principal_cut_length (I : Ideal A) (x : A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x}) := by
  have hmap : (Ideal.span {x}).map (Ideal.Quotient.mk I) =
      Ideal.span {Ideal.Quotient.mk I x} := by
    simp only [Ideal.map_span, Set.image_singleton]
  exact (quotient_cut_length I (Ideal.span {x})).trans
    (Submodule.quotEquivOfEq _ _ hmap).length_eq

theorem quotient_prime_cut_length (I P : Ideal A) (hIP : I ≤ P) (x : A) :
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x})) := by
  have hleft : I ⊔ (P ⊔ Ideal.span {x}) = P ⊔ Ideal.span {x} :=
    sup_eq_right.mpr (hIP.trans le_sup_left)
  have hright : (P ⊔ Ideal.span {x}).map (Ideal.Quotient.mk I) =
      P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x} := by
    simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  calc
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
        Module.length A (A ⧸ (I ⊔ (P ⊔ Ideal.span {x}))) :=
      (Submodule.quotEquivOfEq _ _ hleft).length_eq.symm
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P ⊔ Ideal.span {x}).map (Ideal.Quotient.mk I)) :=
      quotient_cut_length I (P ⊔ Ideal.span {x})
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x})) :=
      (Submodule.quotEquivOfEq _ _ hright).length_eq

noncomputable def quotientMinimalPrimesEquiv (I : Ideal A) :
    minimalPrimes (A ⧸ I) ≃ I.minimalPrimes := by
  classical
  let f : minimalPrimes (A ⧸ I) → I.minimalPrimes := fun Q =>
    ⟨Q.val.comap (Ideal.Quotient.mk I), by
      rw [I.minimalPrimes_eq_comap]
      exact ⟨Q.val, Q.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro Q R h
    apply Subtype.ext
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    exact congrArg Subtype.val h
  · intro P
    have hmem : P.val ∈ Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (A ⧸ I) :=
      Eq.mp (congrArg (fun S : Set (Ideal A) => P.val ∈ S) I.minimalPrimes_eq_comap) P.property
    obtain ⟨Q, hQ, hQP⟩ := hmem
    exact ⟨⟨Q, hQ⟩, Subtype.ext hQP⟩

@[simp] theorem quotientMinimalPrimesEquiv_apply (I : Ideal A)
    (Q : minimalPrimes (A ⧸ I)) :
    (quotientMinimalPrimesEquiv I Q).val = Q.val.comap (Ideal.Quotient.mk I) := rfl

theorem quotient_minimal_local_length (I : Ideal A)
    (Q : minimalPrimes (A ⧸ I)) :
    (letI : (quotientMinimalPrimesEquiv I Q).val.IsPrime :=
       (quotientMinimalPrimesEquiv I Q).property.1.1
     Module.length (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val)
       (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val ⧸
        I.map (algebraMap A (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val)))) =
    (letI : Q.val.IsPrime := Q.property.1.1
     Module.length (Localization.AtPrime Q.val)
       (Localization.AtPrime Q.val ⧸ (⊥ : Ideal (A ⧸ I)).map
        (algebraMap (A ⧸ I) (Localization.AtPrime Q.val)))) := by
  let P := (quotientMinimalPrimesEquiv I Q).val
  let : P.IsPrime := (quotientMinimalPrimesEquiv I Q).property.1.1
  let : Q.val.IsPrime := Q.property.1.1
  have hIP : I ≤ P := (quotientMinimalPrimesEquiv I Q).property.1.2
  have hmap : PiExponentSiegel.W23.quotientParameterPrime I P hIP = Q.val := by
    exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q.val
  have hlocal := PiExponentSiegel.W23.quotient_localized_length_eq_explicit I P hIP
  have hprime :
      (⟨PiExponentSiegel.W23.quotientParameterPrime I P hIP,
        PiExponentSiegel.W23.quotientParameterPrime_isPrime I P hIP⟩ : PrimeSpectrum (A ⧸ I)) =
      ⟨Q.val, Q.property.1.1⟩ := PrimeSpectrum.ext hmap
  have hlength := congrArg (fun p : PrimeSpectrum (A ⧸ I) =>
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) hprime
  refine (hlocal.trans hlength).trans ?_
  rw [Ideal.map_bot]
  exact ((⊥ : Submodule (Localization.AtPrime Q.val) (Localization.AtPrime Q.val)).quotEquivOfEqBot
    rfl).length_eq.symm

end PiExponentJets.W28.LocalIntersection

end OAI
