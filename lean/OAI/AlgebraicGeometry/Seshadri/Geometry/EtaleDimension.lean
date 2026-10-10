import Mathlib

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.EtaleDimension
noncomputable section
open IsLocalRing

lemma local_unramified_dimension_le (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)
  have h := Ideal.height_le_height_add_of_liesOver (maximalIdeal R) (maximalIdeal S)
  rw [hm, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  have H : ((maximalIdeal S).height : WithBot ℕ∞) ≤ (maximalIdeal R).height := by exact_mod_cast h
  simpa only [maximalIdeal_height_eq_ringKrullDim] using H

lemma etale_dimension_le (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply (ringKrullDim_le_iff_height_le _).mpr
  intro q hq
  let := hq
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyUnramified R Sq := Algebra.FormallyUnramified.comp R S Sq
  let : Algebra.FormallyUnramified Rp Sq := Algebra.FormallyUnramified.of_restrictScalars R Rp Sq
  have H := local_unramified_dimension_le Rp Sq
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Rp,
    IsLocalization.AtPrime.ringKrullDim_eq_height q Sq] at H
  exact H.trans ((ringKrullDim_le_iff_height_le _).mp le_rfl inferInstance)

lemma etale_polynomial_dimension_le (K S ι : Type*) [Field K] [CommRing S] [Finite ι]
    [Algebra (MvPolynomial ι K) S] [Algebra.Etale (MvPolynomial ι K) S] :
    ringKrullDim S ≤ (Nat.card ι : WithBot ℕ∞) := by
  let := Fintype.ofFinite ι
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial ι K) S
  have h := etale_dimension_le (MvPolynomial ι K) S
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add, ENat.card_eq_coe_fintype_card, Nat.card_eq_fintype_card, WithBot.coe_natCast] using h

lemma etale_surface_dimension_le (K S : Type*) [Field K] [CommRing S]
    [Algebra (MvPolynomial (Fin 2) K) S]
    [Algebra.Etale (MvPolynomial (Fin 2) K) S] : ringKrullDim S ≤ 2 := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial (Fin 2) K) S
  have h := etale_dimension_le (MvPolynomial (Fin 2) K) S
  simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing] using h

end
end MaximalSeshadri.EtaleDimension
end


end
end

end OAI
