import Mathlib
import OAI.AlgebraicGeometry.LogKodaira.Descent
import OAI.AlgebraicGeometry.LogKodaira.Blowup

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u v

namespace ReverseLogKodaira

 

theorem normal_root_zero_test
    {R : Type u} {K : Type v}
    [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsIntegrallyClosed R]
    {m e : ℕ} (hm : 0 < m) (he : m ∣ e)
    {t s : R} (ht : t ≠ 0) (hs : t ^ e ∣ s)
    {r : K} (hr : r ^ m = algebraMap R K s) :
    ∃ c : R, algebraMap R K (t ^ (e / m) * c) = r := by
  obtain ⟨c, hc⟩ := hs
  have htK : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr ht
  have heq : (e / m) * m = e := Nat.div_mul_cancel he
  have hpow : (r / algebraMap R K (t ^ (e / m))) ^ m = algebraMap R K c := by
    rw [div_pow, hr, hc, map_mul, map_pow, map_pow, ← pow_mul, heq]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ htK)
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := R) hm (hpow ▸ isIntegral_algebraMap)
  refine ⟨d, ?_⟩
  rw [map_mul, hd]
  exact mul_div_cancel₀ _ (by simpa only [map_pow] using pow_ne_zero (e / m) htK)

end ReverseLogKodaira

namespace ReverseLogKodaira.PluriformDescent
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization
open FiberChartSpecialization

 

theorem original_fiber_zero_ramified_root_factor
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (m : ℕ) (s : X.RationalPluriform m)
    (y : Y.ComplexPoint) (hy : y.point ∈ D.complement)
    (hzero : FiberVanishesAt f m s y hy)
    (F : FiberModel f.toBoundaryFibration y)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement) (hyU : y.point ∈ U.1)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
    (P : NumeratorChart f.toBoundaryFibration y F U (fiber_dimension_eq f y hy F) m s)
    {B K : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (z : RingHom.ker (complexPointEvaluation y U.1 hyU))
    (g : Γ(X.scheme, P.V.1) →+* B)
    (h : Blowup.Chart (RingHom.ker (complexPointEvaluation y U.1 hyU)) z →+* B)
    (square : g.comp (f.hom.appLE U.1 P.V.1 P.overOpen).hom =
      h.comp (Blowup.chartMap (RingHom.ker (complexPointEvaluation y U.1 hyU)) z))
    {e : ℕ} (hm : 0 < m) (he : m ∣ e) (τ : B) (hτ : τ ≠ 0)
    (ramification : h (Blowup.chartMap
      (RingHom.ker (complexPointEvaluation y U.1 hyU)) z z) = τ ^ e) :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, P.V.1) :=
      (f.hom.appLE U.1 P.V.1 P.overOpen).hom.toAlgebra
    letI : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, P.V.1) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        (appLE_constants f.hom f.over_base U.1 P.V.1 P.overOpen a).symm
    letI := P.formallySmooth
    ∀ r : K,
      r ^ m = algebraMap B K (g (pluricanonicalCoordinate
        ℂ Γ(Y.scheme, U.1) Γ(X.scheme, P.V.1)
        Y.dimension F.variety.dimension m b P.relativeBasis P.numerator)) →
      ∃ c : B, algebraMap B K (τ ^ (e / m) * c) = r := by
  let : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, P.V.1) :=
    (f.hom.appLE U.1 P.V.1 P.overOpen).hom.toAlgebra
  let : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, P.V.1) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (appLE_constants f.hom f.over_base U.1 P.V.1 P.overOpen a).symm
  let := P.formallySmooth
  intro r hr
  have hmem := original_coefficient_in_point_ideal_of_fiber_zero
    f m s y hy hzero F U hU hyU b P
  have hdiv := Blowup.parameter_dvd_image
    (RingHom.ker (complexPointEvaluation y U.1 hyU)) z
    (f.hom.appLE U.1 P.V.1 P.overOpen).hom g h square hmem
  rw [ramification] at hdiv
  exact normal_root_zero_test hm he hτ hdiv hr

end ReverseLogKodaira.PluriformDescent

end

end OAI
