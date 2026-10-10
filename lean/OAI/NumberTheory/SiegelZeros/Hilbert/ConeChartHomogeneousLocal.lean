import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Intersection.ConeProjectivePoint
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.AffineProjChartPolynomialEquiv

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets.Geometry

open MvPolynomial HomogeneousLocalization _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra coneIdeal_isPrime

universe uProjLocal

noncomputable def coneChartToHomogeneousLocal {K σ : Type uProjLocal} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    affineProjChart K σ →+*
      HomogeneousLocalization.AtPrime (homogeneousSubmodule (Option σ) K) (coneIdeal p) :=
  HomogeneousLocalization.mapId _
    (Submonoid.powers_le.mpr (X_none_not_mem_coneIdeal p))

theorem projectiveLocal_isLocalization {K σ : Type uProjLocal} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    @IsLocalization (affineProjChart K σ) _
      (p.comap (affineProjChartPolynomialEquiv (K := K) (σ := σ)).toRingHom).primeCompl
      (HomogeneousLocalization.AtPrime (homogeneousSubmodule (Option σ) K) (coneIdeal p)) _
      (coneChartToHomogeneousLocal p).toAlgebra := by
  let C := affineProjChart K σ
  let H := HomogeneousLocalization.AtPrime (homogeneousSubmodule (Option σ) K) (coneIdeal p)
  let : Algebra C H := (coneChartToHomogeneousLocal p).toAlgebra
  let x : ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Option σ) K) (X (none : Option σ)) :=
    ⟨coneProjectivePoint p, coneProjectivePoint_mem_basicOpen p⟩
  let q : Ideal C := ((ProjectiveSpectrum.Proj.toSpec (homogeneousSubmodule (Option σ) K)
    (X (none : Option σ))).base x).asIdeal
  have hq : q = p.comap (affineProjChartPolynomialEquiv (K := K) (σ := σ)).toRingHom := by
    change (Proj.basicOpenToSpec (homogeneousSubmodule (Option σ) K) (X (none : Option σ))
      ⟨coneProjectivePoint p, coneProjectivePoint_mem_basicOpen p⟩).asIdeal = _
    rw [basicOpenToSpec_coneProjectivePoint]
    rfl
  let : q.IsPrime := by rw [hq]; infer_instance
  have hM : q.primeCompl =
      (p.comap (affineProjChartPolynomialEquiv (K := K) (σ := σ)).toRingHom).primeCompl := by
    apply Submonoid.ext
    intro z
    change z ∉ q ↔ z ∉ p.comap (affineProjChartPolynomialEquiv (K := K) (σ := σ)).toRingHom
    rw [hq]
  have h : @IsLocalization C _ q.primeCompl H _ (coneChartToHomogeneousLocal p).toAlgebra :=
    ProjectiveSpectrum.Proj.isLocalization_atPrime (homogeneousSubmodule (Option σ) K)
      (X (none : Option σ)) x (isHomogeneous_X K (none : Option σ))
      (show 0 < (1 : ℕ) by decide)
  rw [hM] at h
  exact h

noncomputable def projectiveLocalPolynomialEquiv {K σ : Type uProjLocal} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    HomogeneousLocalization.AtPrime (homogeneousSubmodule (Option σ) K) (coneIdeal p) ≃+*
      Localization.AtPrime p := by
  let C := affineProjChart K σ
  let H := HomogeneousLocalization.AtPrime (homogeneousSubmodule (Option σ) K) (coneIdeal p)
  let : Algebra C H := (coneChartToHomogeneousLocal p).toAlgebra
  let e : C ≃+* MvPolynomial σ K := affineProjChartPolynomialEquiv
  let : IsLocalization (p.comap e.toRingHom).primeCompl H := projectiveLocal_isLocalization p
  refine IsLocalization.ringEquivOfRingEquiv (M := (p.comap e.toRingHom).primeCompl)
    (T := p.primeCompl) H (Localization.AtPrime p) e ?_
  exact e.map_primeCompl_comap_eq p

theorem projectiveLocalPolynomialEquiv_chart {K σ : Type uProjLocal} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (z : affineProjChart K σ) :
    projectiveLocalPolynomialEquiv p (coneChartToHomogeneousLocal p z) =
      algebraMap (MvPolynomial σ K) (Localization.AtPrime p)
        (affineProjChartMap (k := K) (fun i : σ => (X i : MvPolynomial σ K)) z) := by
  let C := affineProjChart K σ
  let H := HomogeneousLocalization.AtPrime (homogeneousSubmodule (Option σ) K) (coneIdeal p)
  let : Algebra C H := (coneChartToHomogeneousLocal p).toAlgebra
  let e : C ≃+* MvPolynomial σ K := affineProjChartPolynomialEquiv
  let : IsLocalization (p.comap e.toRingHom).primeCompl H := projectiveLocal_isLocalization p
  have hmap : (p.comap e.toRingHom).primeCompl.map e.toMonoidHom = p.primeCompl := by
    exact e.map_primeCompl_comap_eq p
  change IsLocalization.ringEquivOfRingEquiv (M := (p.comap e.toRingHom).primeCompl)
    (T := p.primeCompl) H (Localization.AtPrime p) e hmap (algebraMap C H z) =
      algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (e z)
  exact IsLocalization.ringEquivOfRingEquiv_eq hmap z

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
