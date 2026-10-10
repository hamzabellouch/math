import Mathlib
import OAI.NumberTheory.PrimePackets.RayFrobenius

namespace OAI

noncomputable section
open Module
open scoped NumberField nonZeroDivisors

namespace PrimeDegreePackets
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E]

lemma unramified_of_absDiscr_not_mem (F E : Type*)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Ideal (𝓞 F)) (Q : Ideal (𝓞 E)) [Q.IsPrime]
    (hQ : Q.under (𝓞 F) = P) (hD : ((NumberField.discr E).natAbs : 𝓞 F) ∉ P) :
    Algebra.IsUnramifiedAt (𝓞 F) Q := by
  have hDE : ((NumberField.discr E).natAbs : 𝓞 E) ∉ Q := by
    intro h
    apply hD
    rw [← hQ]
    change algebraMap (𝓞 F) (𝓞 E) _ ∈ Q
    simpa only [map_natCast] using h
  have hnot : ¬ Q ∣ differentIdeal ℤ (𝓞 E) := by
    intro h
    apply hDE
    apply (Ideal.dvd_iff_le.mp h)
    rw [← NumberField.absNorm_differentIdeal E (𝓞 E)]
    exact Ideal.absNorm_mem _
  have : Algebra.IsUnramifiedAt ℤ Q := not_dvd_differentIdeal_iff.mp hnot
  exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ Q

lemma unramified_of_principal_congruence (a : 𝓞 F)
    (hc : a - 1 ∈ ThetaConstruction.rationalModulusIdeal (𝓞 F) (NumberField.discr E).natAbs)
    (P : Ideal (𝓞 F)) [P.IsPrime] (ha : a ∈ P)
    (Q : Ideal (𝓞 E)) [Q.IsPrime] (hQ : Q.under (𝓞 F) = P) :
    Algebra.IsUnramifiedAt (𝓞 F) Q := by
  apply unramified_of_absDiscr_not_mem F E P Q hQ
  intro hN
  have hle : ThetaConstruction.rationalModulusIdeal (𝓞 F) (NumberField.discr E).natAbs ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr hN
  have hone : (1 : 𝓞 F) ∈ P := by
    simpa only [sub_sub_cancel] using P.sub_mem ha (hle hc)
  exact Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one P).mpr hone)

lemma principal_count_ne_zero_iff_mem (a : 𝓞 F) (ha : a ≠ 0)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F P (Ideal.span {a}) ≠ 0 ↔ a ∈ P.asIdeal := by
  have hI : Ideal.span {a} ≠ (0 : Ideal (𝓞 F)) := by
    simpa only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using ha
  rw [FractionalIdeal.count_coe F P hI, Int.natCast_ne_zero,
    Associates.count_ne_zero_iff_dvd hI P.irreducible, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem]

lemma unramified_of_principal_count_ne_zero (a : 𝓞 F) (ha : a ≠ 0)
    (hc : a - 1 ∈ ThetaConstruction.rationalModulusIdeal (𝓞 F) (NumberField.discr E).natAbs)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hP : FractionalIdeal.count F P (Ideal.span {a}) ≠ 0)
    (Q : Ideal (𝓞 E)) [Q.IsPrime] (hQ : Q.under (𝓞 F) = P.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 F) Q :=
  unramified_of_principal_congruence F E a hc P.asIdeal
    ((principal_count_ne_zero_iff_mem F a ha P).mp hP) Q hQ

 

theorem principal_congruence_frobenius_product
    [FiniteDimensional F E] [IsGalois F E]
    (χ : (E ≃ₐ[F] E) →* ℂˣ) (a : 𝓞 F) (ha : a ≠ 0)
    (hc : a - 1 ∈ ThetaConstruction.rationalModulusIdeal (𝓞 F)
      (NumberField.discr E).natAbs)
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Ideal (𝓞 E))
    [∀ P, (Q P).IsPrime]
    (hQ : ∀ P, (Q P).under (𝓞 F) = P.asIdeal)
    (τ : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → E ≃ₐ[F] E)
    (hτ : ∀ P, (NumberField.RingOfIntegers.mapAlgHom (τ P)).IsArithFrobAt (Q P)) :
    GaloisIdealCharacter.idealHom F E χ
      (integralIdealFractionalUnit (Ideal.span {a})
        (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha)) =
      ∏ᶠ P, χ (τ P) ^ FractionalIdeal.count F P
        (Ideal.span {a} : FractionalIdeal (𝓞 F)⁰ F) := by
  change (∏ᶠ P, χ (GaloisIdealCharacter.primeFrobenius F E P) ^
    FractionalIdeal.count F P (Ideal.span {a} : FractionalIdeal (𝓞 F)⁰ F)) = _
  apply finprod_congr
  intro P
  by_cases hP : FractionalIdeal.count F P
      (Ideal.span {a} : FractionalIdeal (𝓞 F)⁰ F) = 0
  · simp only [hP, zpow_zero]
  · let : Algebra.IsUnramifiedAt (𝓞 F) (Q P) :=
      unramified_of_principal_count_ne_zero F E a ha hc P hP (Q P) (hQ P)
    have h := GaloisIdealCharacter.idealHom_prime_frobenius F E χ P (Q P) (hQ P)
      (τ P) (hτ P)
    rw [GaloisIdealCharacter.idealHom_prime] at h
    rw [h]

end PrimeDegreePackets

end

end OAI
