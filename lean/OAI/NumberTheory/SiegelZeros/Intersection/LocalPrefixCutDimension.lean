import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.Quotient
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.RegularPrefixLocalization

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W29

open Ideal

section LocalQuotient

variable {S : Type*} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]

theorem local_quotient_cut_dimension_one (I : Ideal S) (x : S)
    (hmin : IsLocalRing.maximalIdeal S ∈ (I ⊔ Ideal.span {x}).minimalPrimes)
    (hinj : Function.Injective (W28.LocalIntersection.quotientMul I x)) :
    ringKrullDim (S ⧸ I) = 1 := by
  have hImax : I ≤ IsLocalRing.maximalIdeal S := le_sup_left.trans hmin.1.2
  have hIne : I ≠ ⊤ := ne_of_lt
    (lt_of_le_of_lt hImax (IsLocalRing.maximalIdeal.isMaximal S).lt_top)
  let : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk I) =
      IsLocalRing.maximalIdeal (S ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hu : ringKrullDim (S ⧸ I) ≤ 1 := by
    have hheight := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
    rw [hmap] at hheight
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact WithBot.coe_le_coe.mpr hheight
  let xb : S ⧸ I := Ideal.Quotient.mk I x
  have hx : x ∈ IsLocalRing.maximalIdeal S :=
    hmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
  have hxb : xb ∈ IsLocalRing.maximalIdeal (S ⧸ I) := by
    rw [← hmap]
    exact Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hx
  have hreg : IsSMulRegular (S ⧸ I) xb := by
    intro y z hyz
    change xb * y = xb * z at hyz
    apply hinj
    change x • y = x • z
    simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hyz
  have hspan : (Ideal.span {xb} : Ideal (S ⧸ I)) ≤
      IsLocalRing.maximalIdeal (S ⧸ I) := (Ideal.span_singleton_le_iff_mem _).mpr hxb
  have hspanne : (Ideal.span {xb} : Ideal (S ⧸ I)) ≠ ⊤ := ne_of_lt
    (lt_of_le_of_lt hspan (IsLocalRing.maximalIdeal.isMaximal (S ⧸ I)).lt_top)
  let : Nontrivial ((S ⧸ I) ⧸ Ideal.span {xb}) :=
    Ideal.Quotient.nontrivial_iff.mpr hspanne
  have hdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hxb
  have hl : 1 ≤ ringKrullDim (S ⧸ I) := by
    rw [← hdrop]
    simpa only [zero_add, add_zero, add_comm] using add_le_add_right
      (ringKrullDim_nonneg_of_nontrivial (R := (S ⧸ I) ⧸ Ideal.span {xb}))
      (1 : WithBot ℕ∞)
  exact le_antisymm hu hl

end LocalQuotient

section Prefix

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem regularPrefix_local_cut_dimension_one
    (T Q : Ideal A) [T.IsPrime] [Q.IsPrime] (hQT : Q ≤ T)
    (gs : List A)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap A (Localization.AtPrime T))))
    (j : ℕ) (hj : j < gs.length)
    (hQ : Q ∈ (Ideal.ofList (gs.take j) ⊔ Ideal.span {gs[j]}).minimalPrimes) :
    ringKrullDim (Localization.AtPrime Q ⧸
      (Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q))) = 1 := by
  let μ := algebraMap A (Localization.AtPrime Q)
  have hmin : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∈
      (((Ideal.ofList (gs.take j)).map μ) ⊔ Ideal.span {μ gs[j]}).minimalPrimes := by
    have hloc : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∈
        ((Ideal.ofList (gs.take j) ⊔ Ideal.span {gs[j]}).map μ).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q)]
      simpa only [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal] using hQ
    simpa only [Ideal.map_sup, Ideal.map_span, Set.image_singleton] using hloc
  exact local_quotient_cut_dimension_one _ _ hmin
    (W16.regularPrefix_quotientMul_injective T Q hQT gs hreg j hj)

end Prefix

end WeightedTorusJets.W29

end

end SiegelZeros

end OAI
