import OAI.AlgebraicGeometry.StableCoordinate.FrameNormalization
import Mathlib.RingTheory.Polynomial.Nilpotent
import Mathlib.Algebra.Polynomial.Laurent

namespace OAI

/-!
# Fiber scaling of normalized polynomial determinant frames

A normalized polynomial lift over the quadric is automatically equivariant for
fiber scaling.  The proof compares the scaled and coefficientwise-transformed
frames over the Laurent coefficient ring; both have the same base and the same
zero-parameter frame.  Unit rigidity gives equality.  No linearity assumption
on the chosen lift is smuggled into the statement.
-/

noncomputable section
namespace StableCoordinate.FrameLift

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp] theorem Frame.map_map (F : Frame R) (f : R →+* S)
    {T : Type*} [CommRing T] (g : S →+* T) :
    (F.map f).map g = F.map (g.comp f) := by
  ext <;> rfl

/-- Fiber scaling does not alter any of the three base coordinates. -/
theorem sameBase_scale (F : Frame R) (q : Rˣ) : SameBase F (F.scale q) := by
  have hm (x y : R) : (↑q * x) * (↑q⁻¹ * y) = x * y := by
    calc
      (↑q * x) * (↑q⁻¹ * y) = (↑q * ↑q⁻¹) * (x * y) := by ring
      _ = x * y := by simp
  exact ⟨(hm _ _).symm, (hm _ _).symm, (hm _ _).symm⟩

/-- Univariate version of normalized-polynomial-frame uniqueness, allowing
any reduced coefficient ring, in particular a Laurent parameter extension. -/
theorem normalized_univariate_unique [IsReduced R] {F G : Frame R[X]}
    (h : SameBase F G)
    (hzero : F.map Polynomial.constantCoeff = G.map Polynomial.constantCoeff) :
    F = G := by
  have hu : IsUnit (comparison F G) := (comparisonUnit h).isUnit
  have hp : comparison F G = C ((comparison F G).coeff 0) := by
    ext n
    by_cases hn : n = 0
    · subst n; simp
    · rw [coeff_C, ite_eq_right hn]
      exact isNilpotent_iff_eq_zero.mp
        ((Polynomial.isUnit_iff_coeff_isUnit_isNilpotent.mp hu).2 n hn)
  have heval : (comparison F G).coeff 0 = 1 := by
    change Polynomial.constantCoeff (comparison F G) = 1
    rw [← comparison_map, hzero, comparison_self]
  apply eq_of_comparison_eq_one h
  simpa only [heval, C_1] using hp

/-- Coefficientwise ring maps commute with specialization of a polynomial
family of determinant frames. -/
theorem Frame.map_polynomial_constantCoeff (F : Frame R[X]) (f : R →+* S) :
    (F.map (Polynomial.mapRingHom f)).map Polynomial.constantCoeff =
      (F.map Polynomial.constantCoeff).map f := by
  ext <;> simp [Frame.map, Polynomial.constantCoeff, Polynomial.coeff_map]

/-- Fiber equivariance follows from normalization and equality of the base
coordinates alone.  For the source, `S` is the Laurent extension of `R`, `ι`
is the constant inclusion, `ρ` is fiber scaling, and `q` is its parameter. -/
theorem normalized_frame_scaling [IsReduced S]
    (F : Frame R[X]) (F₀ : Frame R) (ρ ι : R →+* S) (q : Sˣ)
    (hnormal : F.map Polynomial.constantCoeff = F₀)
    (hzero : F₀.map ρ = (F₀.map ι).scale q)
    (hbase : SameBase (F.map (Polynomial.mapRingHom ρ))
      (F.map (Polynomial.mapRingHom ι))) :
    F.map (Polynomial.mapRingHom ρ) =
      (F.map (Polynomial.mapRingHom ι)).scale (Units.map (Polynomial.C : S →+* S[X]).toMonoidHom q) := by
  apply normalized_univariate_unique
  · exact sameBase_trans hbase (sameBase_scale _ _)
  · rw [Frame.map_polynomial_constantCoeff, hnormal, hzero, Frame.map_scale,
      Frame.map_polynomial_constantCoeff, hnormal]
    congr 1
    ext
    simp

/-- If the base coordinate polynomials come from a fixed subring, two coefficient
homomorphisms agreeing on that subring produce frames over the same base. -/
theorem sameBase_map_of_base_polynomials
    {B : Type*} [CommRing B] (F : Frame R[X]) (j : B →+* R)
    (ρ ι : R →+* S) (hbase : ρ.comp j = ι.comp j)
    (x y z : B[X])
    (hx : F.a * F.b = x.map j)
    (hy : F.d * F.c = y.map j)
    (hz : F.d * F.b = z.map j) :
    SameBase (F.map (Polynomial.mapRingHom ρ))
      (F.map (Polynomial.mapRingHom ι)) := by
  have hm (p : B[X]) : (p.map j).map ρ = (p.map j).map ι := by
    rw [Polynomial.map_map, Polynomial.map_map, hbase]
  change (F.a.map ρ) * (F.b.map ρ) = (F.a.map ι) * (F.b.map ι) ∧
    (F.d.map ρ) * (F.c.map ρ) = (F.d.map ι) * (F.c.map ι) ∧
    (F.d.map ρ) * (F.b.map ρ) = (F.d.map ι) * (F.b.map ι)
  simpa only [← Polynomial.map_mul, hx, hy, hz] using
    And.intro (hm x) (And.intro (hm y) (hm z))

/-- Version ready for an algebraic-action lift: the base coordinate
polynomials have been constructed in the base ring, whose scaling is trivial. -/
theorem normalized_frame_scaling_of_base [IsReduced S]
    {B : Type*} [CommRing B] (F : Frame R[X]) (F₀ : Frame R)
    (j : B →+* R) (ρ ι : R →+* S) (q : Sˣ)
    (hbase : ρ.comp j = ι.comp j)
    (x y z : B[X])
    (hx : F.a * F.b = x.map j)
    (hy : F.d * F.c = y.map j)
    (hz : F.d * F.b = z.map j)
    (hnormal : F.map Polynomial.constantCoeff = F₀)
    (hzero : F₀.map ρ = (F₀.map ι).scale q) :
    F.map (Polynomial.mapRingHom ρ) =
      (F.map (Polynomial.mapRingHom ι)).scale
        (Units.map (Polynomial.C : S →+* S[X]).toMonoidHom q) :=
  normalized_frame_scaling F F₀ ρ ι q hnormal hzero
    (sameBase_map_of_base_polynomials F j ρ ι hbase x y z hx hy hz)

/-- The exact coefficient equations implied by frame-scaling equivariance.
The case `n=1` is the infinitesimal fiber-weight preservation statement. -/
theorem coefficient_scaling (F : Frame R[X]) (ρ ι : R →+* S) (q : Sˣ)
    (h : F.map (Polynomial.mapRingHom ρ) =
      (F.map (Polynomial.mapRingHom ι)).scale
        (Units.map (Polynomial.C : S →+* S[X]).toMonoidHom q)) (n : ℕ) :
    ρ (F.a.coeff n) = ↑q * ι (F.a.coeff n) ∧
    ρ (F.d.coeff n) = ↑q * ι (F.d.coeff n) ∧
    ρ (F.b.coeff n) = ↑q⁻¹ * ι (F.b.coeff n) ∧
    ρ (F.c.coeff n) = ↑q⁻¹ * ι (F.c.coeff n) := by
  have ha := congrArg (fun G : Frame S[X] => G.a.coeff n) h
  have hd := congrArg (fun G : Frame S[X] => G.d.coeff n) h
  have hb := congrArg (fun G : Frame S[X] => G.b.coeff n) h
  have hc := congrArg (fun G : Frame S[X] => G.c.coeff n) h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Frame.map, Frame.scale] using ha
  · simpa [Frame.map, Frame.scale] using hd
  · simpa [Frame.map, Frame.scale] using hb
  · simpa [Frame.map, Frame.scale] using hc

end StableCoordinate.FrameLift

end

end OAI
