import OAI.AlgebraicGeometry.StableCoordinate.LocalizationIntersection
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap

namespace OAI

/-!
# The coefficient-ring step in the two-chart rigidity argument

A polynomial chart over a principal localization detects coefficients which
belong to the fraction field of the coefficient ring.  This module proves the
step by denominator clearing.  In particular, it does not require choosing a
common overfield or treating a set-theoretic chart as an algebraic chart.

The intended application is `R = k[a,d,u]` and
`A = k[a,d,b,c,u]/(ac-bd-1)`.  The two actual injective algebra maps to
`R[a⁻¹][b]` and `R[d⁻¹][c]` are supplied by the determinant-ring charts.
-/

namespace StableCoordinate.ChartIntersection

open Polynomial

/-- A polynomial which becomes constant on multiplication by a nonzero
constant was already constant. -/
theorem eq_C_of_mul_C_eq_C {S : Type*} [CommRing S] [NoZeroDivisors S]
    {p : Polynomial S} {r s : S} (hr : r ≠ 0)
    (h : p * C r = C s) : p = C (p.coeff 0) := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  · have hc := congrArg (fun f : Polynomial S => f.coeff n) h
    simp only [coeff_mul_C, coeff_C, ite_eq_right hn] at hc
    simp only [coeff_C, ite_eq_right hn]
    exact (mul_eq_zero.mp hc).resolve_right hr

section Chart

variable {R A S : Type*} [CommRing R] [IsDomain R]
  [CommRing A] [Algebra R A]
  [CommRing S] [IsDomain S] [Algebra R S]
  {a : R} [IsLocalization.Away a S]

omit [IsDomain S] in
/-- The canonical map to a localization away from a nonzero element is injective. -/
theorem away_algebraMap_injective (ha : a ≠ 0) :
    Function.Injective (algebraMap R S) := by
  apply IsLocalization.injective (M := Submonoid.powers a) S
  rintro x ⟨m, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m ha)

omit [IsDomain R] [IsDomain S] in
/-- An injective polynomial chart whose value is constant supplies a power
of the localized element as a denominator in the original algebra. -/
theorem has_power_denominator_of_chart_constant
    (e : A →ₐ[R] Polynomial S) (he : Function.Injective e)
    {q : A} {v : S} (hconst : e q = C v) :
    ∃ (m : ℕ) (t : R), q * algebraMap R A (a ^ m) = algebraMap R A t := by
  obtain ⟨m, t, ht⟩ := IsLocalization.Away.surj a v
  refine ⟨m, t, he ?_⟩
  simp only [map_mul, AlgHom.commutes, Polynomial.algebraMap_apply]
  rw [hconst, ← map_mul, map_pow]
  exact congrArg C ht

/-- If an element of an algebra is a fraction over the coefficient ring, an
injective polynomial chart over `R[a⁻¹]` gives an `a`-power denominator.
This is the precise content of "there are no b terms" in Section 5. -/
theorem has_power_denominator_of_chart
    (ha : a ≠ 0) (e : A →ₐ[R] Polynomial S) (he : Function.Injective e)
    {q : A} {r s : R} (hr : r ≠ 0)
    (h : q * algebraMap R A r = algebraMap R A s) :
    ∃ (m : ℕ) (t : R), q * algebraMap R A (a ^ m) = algebraMap R A t := by
  have hinj : Function.Injective (algebraMap R S) := away_algebraMap_injective ha
  have hrS : algebraMap R S r ≠ 0 := by
    exact fun h0 => hr (hinj (by simpa using h0))
  have hchart : e q * C (algebraMap R S r) = C (algebraMap R S s) := by
    simpa only [map_mul, AlgHom.commutes, Polynomial.algebraMap_apply] using congrArg e h
  have hconst : e q = C ((e q).coeff 0) := eq_C_of_mul_C_eq_C hrS hchart
  exact has_power_denominator_of_chart_constant e he hconst

end Chart

section Intersection

variable {R A S T : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]
  [CommRing A] [IsDomain A] [Algebra R A]
  [CommRing S] [IsDomain S] [Algebra R S]
  [CommRing T] [IsDomain T] [Algebra R T]
  {a d : R} [IsLocalization.Away a S] [IsLocalization.Away d T]

omit [IsDomain S] [IsDomain T] in
/-- A constant in both polynomial charts lies in the base ring.  This
version is suited to locally nilpotent derivations of the two chart rings,
which directly show that both chart images of the rigidity coefficient are
constant; no common fraction field needs to be constructed. -/
theorem mem_range_of_two_constant_charts
    (ha : a ≠ 0) (had : IsRelPrime a d)
    (e : A →ₐ[R] Polynomial S) (he : Function.Injective e)
    (f : A →ₐ[R] Polynomial T) (hf : Function.Injective f)
    {q : A} {v : S} {w : T} (hq : e q = C v) (hq' : f q = C w) :
    q ∈ Set.range (algebraMap R A) := by
  obtain ⟨m, u, hu⟩ := has_power_denominator_of_chart_constant (a := a) e he hq
  obtain ⟨n, v, hv⟩ := has_power_denominator_of_chart_constant (a := d) f hf hq'
  have hbase : Function.Injective (algebraMap R A) := by
    intro x y hxy
    apply away_algebraMap_injective (S := S) ha
    apply Polynomial.C_injective
    simpa only [AlgHom.commutes, Polynomial.algebraMap_apply] using congrArg e hxy
  exact exists_algebraMap_eq_of_two_power_denominators hbase ha had hu hv

/-- Two injective polynomial charts at relatively prime coefficient variables
force the intersection with the coefficient fraction field to be the original
coefficient ring.  The fraction-field condition is encoded without an overfield
as the equation `q*r=s` with `r ≠ 0`. -/
theorem mem_range_of_fraction_eq_of_two_charts
    (ha : a ≠ 0) (hd : d ≠ 0) (had : IsRelPrime a d)
    (e : A →ₐ[R] Polynomial S) (he : Function.Injective e)
    (f : A →ₐ[R] Polynomial T) (hf : Function.Injective f)
    {q : A} {r s : R} (hr : r ≠ 0)
    (h : q * algebraMap R A r = algebraMap R A s) :
    q ∈ Set.range (algebraMap R A) := by
  obtain ⟨m, u, hu⟩ := has_power_denominator_of_chart ha e he hr h
  obtain ⟨n, v, hv⟩ := has_power_denominator_of_chart hd f hf hr h
  have hbase : Function.Injective (algebraMap R A) := by
    intro x y hxy
    apply away_algebraMap_injective (S := S) ha
    apply Polynomial.C_injective
    simpa only [AlgHom.commutes, Polynomial.algebraMap_apply] using congrArg e hxy
  exact exists_algebraMap_eq_of_two_power_denominators hbase ha had hu hv

end Intersection

section RingCharts

variable {R A S T : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]
  [CommRing A] [IsDomain A]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  {a d : R} [IsLocalization.Away a S] [IsLocalization.Away d T]

/-- Ring-homomorphism interface for actual quotient charts.  The commuting
squares are explicit, so callers do not have to install an algebra structure
on the hypersurface over its polynomial coefficient subring. -/
theorem exists_base_of_two_ring_charts
    (ι : R →+* A) (ha : a ≠ 0) (had : IsRelPrime a d)
    (e : A →+* Polynomial S) (he : Function.Injective e)
    (f : A →+* Polynomial T) (hf : Function.Injective f)
    (heBase : ∀ r, e (ι r) = Polynomial.C (algebraMap R S r))
    (hfBase : ∀ r, f (ι r) = Polynomial.C (algebraMap R T r))
    {q : A} {v : S} {w : T}
    (hq : e q = Polynomial.C v) (hq' : f q = Polynomial.C w) :
    ∃ t : R, ι t = q := by
  let : Algebra R A := ι.toAlgebra
  let e' : A →ₐ[R] Polynomial S :=
    { e with commutes' := heBase }
  let f' : A →ₐ[R] Polynomial T :=
    { f with commutes' := hfBase }
  exact mem_range_of_two_constant_charts ha had e' he f' hf hq hq'

end RingCharts

end StableCoordinate.ChartIntersection

end OAI
