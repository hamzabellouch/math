import Mathlib.RingTheory.Localization.LocalizationLocalization
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialAssociatedLocalization

namespace OAI

noncomputable section
namespace PiExponentJets.W16

open RingTheory.Sequence

variable {A : Type*} [CommRing A]

theorem weaklyRegular_atPrime_mono
    (T Q : Ideal A) [T.IsPrime] [Q.IsPrime] (hQT : Q ≤ T)
    (gs : List A)
    (hreg : IsWeaklyRegular (Localization.AtPrime T)
      (gs.map (algebraMap A (Localization.AtPrime T)))) :
    IsWeaklyRegular (Localization.AtPrime Q)
      (gs.map (algebraMap A (Localization.AtPrime Q))) := by
  have hc : T.primeCompl ≤ Q.primeCompl := by
    intro a ha
    exact fun h => ha (hQT h)
  let : Algebra (Localization.AtPrime T) (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.AtPrime T) (Localization.AtPrime Q) T.primeCompl Q.primeCompl hc
  let : IsScalarTower A (Localization.AtPrime T) (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.AtPrime T) (Localization.AtPrime Q) T.primeCompl Q.primeCompl hc
  let : IsLocalization
      (Q.primeCompl.map (algebraMap A (Localization.AtPrime T)))
      (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le
      (Localization.AtPrime T) (Localization.AtPrime Q) T.primeCompl Q.primeCompl hc
  let : Module.Flat (Localization.AtPrime T) (Localization.AtPrime Q) :=
    IsLocalization.flat (Localization.AtPrime Q)
      (Q.primeCompl.map (algebraMap A (Localization.AtPrime T)))
  have hh := PiExponentSiegel.W58.weaklyRegular_map_of_flat
    (S := Localization.AtPrime Q)
    (gs.map (algebraMap A (Localization.AtPrime T))) hreg
  have hmaps :
      (gs.map (algebraMap A (Localization.AtPrime T))).map
        (algebraMap (Localization.AtPrime T) (Localization.AtPrime Q)) =
      gs.map (algebraMap A (Localization.AtPrime Q)) := by
    simp only [List.map_map]
    congr 1
    funext a
    exact (IsScalarTower.algebraMap_apply A
      (Localization.AtPrime T) (Localization.AtPrime Q) a).symm
  rw [hmaps] at hh
  exact hh

theorem regularPrefix_quotientMul_injective
    (T Q : Ideal A) [T.IsPrime] [Q.IsPrime] (hQT : Q ≤ T)
    (gs : List A)
    (hreg : IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap A (Localization.AtPrime T))))
    (j : ℕ) (hj : j < gs.length) :
    Function.Injective
      (W28.LocalIntersection.quotientMul
        ((Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q)))
        (algebraMap A (Localization.AtPrime Q) gs[j])) := by
  have hw := weaklyRegular_atPrime_mono T Q hQT gs hreg.toIsWeaklyRegular
  have hm := hw.regular_mod_prev j (by simpa only [List.length_map] using hj)
  have he :
      (Ideal.ofList ((gs.map (algebraMap A (Localization.AtPrime Q))).take j) •
        (⊤ : Submodule (Localization.AtPrime Q) (Localization.AtPrime Q))) =
      (Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q)) := by
    change Ideal.ofList ((gs.map (algebraMap A (Localization.AtPrime Q))).take j) *
      (⊤ : Ideal (Localization.AtPrime Q)) = _
    rw [Ideal.mul_top, Ideal.map_ofList, List.map_take]
  have hm' : IsSMulRegular
      (Localization.AtPrime Q ⧸
        (Ideal.ofList ((gs.map (algebraMap A (Localization.AtPrime Q))).take j) •
          (⊤ : Submodule (Localization.AtPrime Q) (Localization.AtPrime Q))))
      (algebraMap A (Localization.AtPrime Q) gs[j]) := by
    simpa only [List.getElem_map] using hm
  change IsSMulRegular
    (Localization.AtPrime Q ⧸
      (Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q)))
    (algebraMap A (Localization.AtPrime Q) gs[j])
  exact ((Submodule.quotEquivOfEq _ _ he).isSMulRegular_congr
    (algebraMap A (Localization.AtPrime Q) gs[j])).mp hm'

end PiExponentJets.W16

end

end OAI
