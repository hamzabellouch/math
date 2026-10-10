import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Localization.FractionRing

namespace OAI

/-!
# Constants in polynomial charts

Section 5 identifies two localizations of the determinant ring with polynomial
rings over principal localizations of `k[a,d,u]`.  The needed intersection with
`k(a,d,u)` is not a set-theoretic assertion: a polynomial over the chart's
coefficient ring which becomes constant over the fraction field has that
constant in its coefficient ring.  The lemmas here prove that exact algebraic
interface without assuming the manuscript's chart identifications.
-/

namespace StableCoordinate.PolynomialChartIntersection

open Polynomial

section RingHom

variable {R S : Type*} [Semiring R] [Semiring S]

/-- Taking the constant coefficient recovers a constant in the range of an
actual polynomial coefficient map.  No injectivity assumption is needed. -/
theorem constant_mem_range_map_iff (f : R →+* S) (s : S) :
    C s ∈ Set.range (Polynomial.map f) ↔ s ∈ Set.range f := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff 0, ?_⟩
    simpa only [coeff_map, coeff_C_zero] using congrArg (fun q : S[X] ↦ q.coeff 0) hp
  · rintro ⟨r, rfl⟩
    exact ⟨C r, map_C f⟩

/-- A mapped polynomial that becomes constant was itself constant when the
coefficient map is injective. -/
theorem map_eq_C_iff (f : R →+* S) (hf : Function.Injective f)
    (p : R[X]) (s : S) :
    Polynomial.map f p = C s ↔ ∃ r : R, p = C r ∧ f r = s := by
  constructor
  · intro h
    have hr : f (p.coeff 0) = s := by
      simpa only [coeff_map, coeff_C_zero] using congrArg (fun q : S[X] ↦ q.coeff 0) h
    use p.coeff 0
    refine ⟨?_, hr⟩
    apply Polynomial.map_injective f hf
    rw [h, map_C, hr]
  · rintro ⟨r, rfl, rfl⟩
    exact map_C f

/-- The intersection of coefficientwise images with the constant polynomials
is exactly the image of the original coefficient ring. -/
theorem polynomial_range_inf_constants (f : R →+* S) :
    (Polynomial.mapRingHom f).rangeS ⊓ (C : S →+* S[X]).rangeS =
      ((C : S →+* S[X]).comp f).rangeS := by
  ext p
  constructor
  · rintro ⟨⟨r, hr⟩, ⟨s, rfl⟩⟩
    obtain ⟨a, ha⟩ := (constant_mem_range_map_iff f s).mp ⟨r, hr⟩
    exact ⟨a, by simp only [RingHom.comp_apply, ha]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨⟨C r, map_C f⟩, ⟨f r, rfl⟩⟩

end RingHom

end StableCoordinate.PolynomialChartIntersection

namespace StableCoordinate.PolynomialChartIntersection

open Polynomial

section CompatibleCharts

variable {A C K Ω : Type*} [Semiring A] [Semiring C] [Semiring K] [Semiring Ω]

/-- If a polynomial chart and a coefficient-field embedding agree in a common
ambient ring, injectivity of the polynomial chart forces the putative constant
to belong to the chart coefficient ring.  All maps and commuting-square
conditions are explicit; no identification of abstractly isomorphic rings is
silently used. -/
theorem mem_coefficient_range_of_compatible_chart
    (f : A →+* K) (chart : C →+* A[X])
    (inclusion : C →+* Ω) (coefficients : K →+* Ω)
    (polynomialEmbedding : K[X] →+* Ω)
    (hinj : Function.Injective polynomialEmbedding)
    (hchart : (polynomialEmbedding.comp (Polynomial.mapRingHom f)).comp chart = inclusion)
    (hcoeff : polynomialEmbedding.comp (Polynomial.C : K →+* K[X]) = coefficients)
    {c : C} {q : K} (h : inclusion c = coefficients q) :
    q ∈ Set.range f := by
  apply (constant_mem_range_map_iff f q).mp
  refine ⟨chart c, hinj ?_⟩
  calc
    polynomialEmbedding (Polynomial.map f (chart c)) = inclusion c :=
      RingHom.congr_fun hchart c
    _ = coefficients q := h
    _ = polynomialEmbedding (Polynomial.C q) := (RingHom.congr_fun hcoeff q).symm

/-- The previous lemma also records the stronger conclusion that the chart
polynomial itself is constant whenever its coefficient map is injective. -/
theorem chart_eq_constant_of_compatible_chart
    (f : A →+* K) (hf : Function.Injective f) (chart : C →+* A[X])
    (inclusion : C →+* Ω) (coefficients : K →+* Ω)
    (polynomialEmbedding : K[X] →+* Ω)
    (hinj : Function.Injective polynomialEmbedding)
    (hchart : (polynomialEmbedding.comp (Polynomial.mapRingHom f)).comp chart = inclusion)
    (hcoeff : polynomialEmbedding.comp (Polynomial.C : K →+* K[X]) = coefficients)
    {c : C} {q : K} (h : inclusion c = coefficients q) :
    ∃ a : A, chart c = Polynomial.C a ∧ f a = q := by
  apply (map_eq_C_iff f hf _ _).mp
  apply hinj
  calc
    polynomialEmbedding (Polynomial.map f (chart c)) = inclusion c :=
      RingHom.congr_fun hchart c
    _ = coefficients q := h
    _ = polynomialEmbedding (Polynomial.C q) := (RingHom.congr_fun hcoeff q).symm

end CompatibleCharts

section AlgebraHom

variable {k R S : Type*} [CommSemiring k] [Semiring R] [Semiring S]
  [Algebra k R] [Algebra k S]

/-- The constants-in-chart statement in the form of an equality of
`k`-subalgebras, for direct use with affine coordinate rings. -/
theorem polynomial_algRange_inf_constants (f : R →ₐ[k] S) :
    (Polynomial.mapAlgHom f).range ⊓ (Polynomial.CAlgHom : S →ₐ[k] S[X]).range =
      ((Polynomial.CAlgHom : S →ₐ[k] S[X]).comp f).range := by
  ext p
  constructor
  · rintro ⟨⟨r, hr⟩, ⟨s, rfl⟩⟩
    obtain ⟨a, ha⟩ := (constant_mem_range_map_iff f.toRingHom s).mp ⟨r, hr⟩
    exact ⟨a, congrArg (Polynomial.C : S → S[X]) ha⟩
  · rintro ⟨r, rfl⟩
    exact ⟨⟨C r, map_C f.toRingHom⟩, ⟨f r, rfl⟩⟩

end AlgebraHom

end StableCoordinate.PolynomialChartIntersection

end OAI
