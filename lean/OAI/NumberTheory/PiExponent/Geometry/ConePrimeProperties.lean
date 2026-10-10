import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.Submodule
import OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] MvPolynomial.gradedAlgebra

section General

variable {A B : Type*} [CommRing A] [CommRing B]

theorem mapped_minimalPrime_of_prime_extension
    (f : A →+* B) {I P : Ideal A} (hP : P ∈ I.minimalPrimes)
    (hprime : (P.map f).IsPrime) (hcontract : (P.map f).comap f = P) :
    P.map f ∈ (I.map f).minimalPrimes := by
  refine ⟨⟨hprime, Ideal.map_mono hP.1.2⟩, ?_⟩
  intro Q hQ hQP
  apply Ideal.map_le_iff_le_comap.mpr
  apply hP.2 ⟨hQ.1.comap f, Ideal.map_le_iff_le_comap.mp hQ.2⟩
  exact (Ideal.comap_mono hQP).trans hcontract.le

theorem minimalPrime_isHomogeneous {k σ : Type*} [CommRing k]
    (I Q : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) :
    Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := k)
  let C := Q.homogeneousCore (MvPolynomial.homogeneousSubmodule σ k)
  have hIC : I ≤ C.toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hQ.1.2
  have hCQ : C.toIdeal ≤ Q := Ideal.toIdeal_homogeneousCore_le _ _
  have hQC : Q ≤ C.toIdeal := hQ.2 ⟨hQ.1.1.homogeneousCore, hIC⟩ hCQ
  have heq : C.toIdeal = Q := le_antisymm hCQ hQC
  exact heq ▸ C.isHomogeneous

end General

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem conePrime_minimal_over_homogenized {ι : Type*} (f : ι → AffineRing k σ)
    (hP : P ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    conePrime k σ P ∈
      (Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))).minimalPrimes := by
  let H := Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))
  have hLP : laurentPrime (AffineRing k σ) P ∈ (H.map (coneToLaurent k σ)).minimalPrimes := by
    rw [map_homogenized_span_eq_laurent_span k σ f]
    exact mapped_minimalPrime_of_prime_extension LaurentPolynomial.C hP inferInstance
      (laurentPrime_comap (AffineRing k σ) P)
  have hcomp : coneToLaurent k σ = (coneLaurentEquiv k σ).toRingHom.comp
      (algebraMap (ConeRing k σ) (ConeAway k σ)) := by
    apply RingHom.ext
    intro F
    exact (coneAwayToLaurent_algebraMap k σ F).symm
  have hI : (H.map (coneToLaurent k σ)).comap (coneLaurentEquiv k σ).toRingHom =
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ)) := by
    rw [hcomp, ← Ideal.map_map]
    simp only [RingEquiv.toRingHom_eq_coe]
    rw [Ideal.map_comap_of_equiv]
    apply Ideal.ext
    intro z
    change (coneLaurentEquiv k σ).symm ((coneLaurentEquiv k σ) z) ∈
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ)) ↔ z ∈
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ))
    rw [RingEquiv.symm_apply_apply]
  have hchart := Ideal.minimalPrimes_comap_of_surjective
    (coneLaurentEquiv k σ).surjective hLP
  change awayChartPrime k σ P ∈
    ((H.map (coneToLaurent k σ)).comap (coneLaurentEquiv k σ).toRingHom).minimalPrimes at hchart
  rw [hI, IsLocalization.minimalPrimes_map
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ)) (ConeAway k σ)] at hchart
  exact hchart

theorem homogenized_span_isHomogeneous {ι : Type*} (f : ι → AffineRing k σ) :
    (Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option σ) k) := by
  let := MvPolynomial.gradedAlgebra (σ := Option σ) (R := k)
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Option σ) k)
  rintro F ⟨i, rfl⟩
  exact ⟨(f i).totalDegree, PiExponentJets.W22.homogenize_isHomogeneous (f i)⟩

theorem conePrime_isHomogeneous_of_minimal {ι : Type*} (f : ι → AffineRing k σ)
    (hP : P ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    (conePrime k σ P).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Option σ) k) :=
  minimalPrime_isHomogeneous _ _ (homogenized_span_isHomogeneous k σ f)
    (conePrime_minimal_over_homogenized k σ P f hP)

variable [IsNoetherianRing (AffineRing k σ)]

theorem laurentPrime_height_eq :
    (laurentPrime (AffineRing k σ) P).height = P.height := by
  let : IsNoetherianRing (LaurentChart k σ) :=
    IsLocalization.isNoetherianRing
      (Submonoid.powers (Polynomial.X : Polynomial (AffineRing k σ)))
      (LaurentChart k σ) inferInstance
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    P (laurentPrime (AffineRing k σ) P)
  change (laurentPrime (AffineRing k σ) P).height = P.height +
    ((laurentPrime (AffineRing k σ) P).map
      (Ideal.Quotient.mk (laurentPrime (AffineRing k σ) P))).height at h
  simpa only [Ideal.map_quotient_self, Ideal.height_bot, add_zero] using h

theorem conePrime_height_eq : (conePrime k σ P).height = P.height := by
  change ((awayChartPrime k σ P).comap
    (algebraMap (ConeRing k σ) (ConeAway k σ))).height = P.height
  rw [IsLocalization.height_under
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ))]
  change ((laurentPrime (AffineRing k σ) P).comap (coneLaurentEquiv k σ).toRingHom).height = _
  exact ((coneLaurentEquiv k σ).height_comap (laurentPrime (AffineRing k σ) P)).trans
    (laurentPrime_height_eq k σ P)

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
