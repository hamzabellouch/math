import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Tactic

namespace OAI

/-!
# Uniqueness of normalized polynomial lifts of determinant frames

The bundle in the source is described by `a*c - b*d = 1`, with base
coordinates `a*b`, `d*c`, and `d*b`.  This file proves directly in rings
that two frames over the same base differ by a unit.  Consequently two
polynomial families over a reduced ring, having the same base and the
same specialization at the zero parameter, agree.  In the action-lift
argument this is the algebraic group-law normalization step; the
existence of a lifted polynomial family is a separate obligation.
-/

namespace StableCoordinate
namespace FrameLift

/-- A frame for the rank-one bundle underlying the determinant presentation. -/
structure Frame (R : Type*) [CommRing R] where
  a : R
  d : R
  b : R
  c : R
  determinant : a * c - b * d = 1

variable {R S : Type*} [CommRing R] [CommRing S]

@[ext]
theorem Frame.ext {F G : Frame R}
    (ha : F.a = G.a) (hd : F.d = G.d) (hb : F.b = G.b) (hc : F.c = G.c) :
    F = G := by cases F; cases G; simp_all

/-- Extend each coordinate of a frame by a ring homomorphism. -/
def Frame.map (f : R →+* S) (F : Frame R) : Frame S where
  a := f F.a
  d := f F.d
  b := f F.b
  c := f F.c
  determinant := by simpa only [← map_mul, ← map_sub, map_one] using congrArg f F.determinant

/-- Equality of the three quadric base coordinates. -/
def SameBase (F G : Frame R) : Prop :=
  F.a * F.b = G.a * G.b ∧ F.d * F.c = G.d * G.c ∧ F.d * F.b = G.d * G.b

/-- Concrete scalar comparing two frames over the same base. -/
def comparison (F G : Frame R) : R := F.c * G.a - F.b * G.d

theorem sameBase_symm {F G : Frame R} (h : SameBase F G) : SameBase G F :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem comparison_a {F G : Frame R} (h : SameBase F G) :
    comparison F G * F.a = G.a := by
  dsimp [comparison]
  linear_combination G.a * F.determinant + G.a * h.2.2 - G.d * h.1

theorem comparison_d {F G : Frame R} (h : SameBase F G) :
    comparison F G * F.d = G.d := by
  dsimp [comparison]
  linear_combination G.a * h.2.1 + G.d * G.determinant - G.d * h.2.2

theorem comparison_b {F G : Frame R} (h : SameBase F G) :
    comparison G F * F.b = G.b := by
  dsimp [comparison]
  linear_combination G.c * h.1 + G.b * G.determinant - G.b * h.2.2

theorem comparison_c {F G : Frame R} (h : SameBase F G) :
    comparison G F * F.c = G.c := by
  dsimp [comparison]
  linear_combination G.c * F.determinant + G.c * h.2.2 - G.b * h.2.1

/-- The two comparison scalars are inverse units, without any domain hypothesis. -/
theorem comparison_mul_reverse {F G : Frame R} (h : SameBase F G) :
    comparison F G * comparison G F = 1 := by
  calc
    comparison F G * comparison G F =
        comparison F G * comparison G F * (F.a * F.c - F.b * F.d) := by
      rw [F.determinant, mul_one]
    _ = (comparison F G * F.a) * (comparison G F * F.c) -
        (comparison G F * F.b) * (comparison F G * F.d) := by ring
    _ = 1 := by
      rw [comparison_a h, comparison_c h, comparison_b h, comparison_d h, G.determinant]

/-- The unique unit changing one frame into the other. -/
def comparisonUnit {F G : Frame R} (h : SameBase F G) : Rˣ where
  val := comparison F G
  inv := comparison G F
  val_inv := comparison_mul_reverse h
  inv_val := comparison_mul_reverse (sameBase_symm h)

@[simp]
theorem comparison_self (F : Frame R) : comparison F F = 1 := by
  simpa only [comparison, mul_comm F.c F.a] using F.determinant

@[simp]
theorem comparison_map (f : R →+* S) (F G : Frame R) :
    comparison (F.map f) (G.map f) = f (comparison F G) := by
  simp only [comparison, Frame.map, map_sub, map_mul]

/-- The scalar is determined by its action on the two positive-weight coordinates. -/
theorem comparison_unique (F G : Frame R) {q : R}
    (ha : q * F.a = G.a) (hd : q * F.d = G.d) : q = comparison F G := by
  dsimp [comparison]
  linear_combination -q * F.determinant + F.c * ha - F.b * hd

/-- Comparison scalar one forces equality of the entire frame. -/
theorem eq_of_comparison_eq_one {F G : Frame R} (h : SameBase F G)
    (hq : comparison F G = 1) : F = G := by
  have hrev : comparison G F = 1 := by
    simpa only [hq, one_mul] using comparison_mul_reverse h
  apply Frame.ext
  · simpa only [hq, one_mul] using comparison_a h
  · simpa only [hq, one_mul] using comparison_d h
  · simpa only [hrev, one_mul] using comparison_b h
  · simpa only [hrev, one_mul] using comparison_c h

/-- Two polynomial families of frames over a reduced coefficient ring are equal
if they have the same base coordinates and agree at the zero parameter.

In particular this proves the group law for a normalized polynomial-family lift:
compare the iterated lift over two parameters with the lift at their sum. -/
theorem normalized_polynomial_unique {σ : Type*} [IsReduced R]
    {F G : Frame (MvPolynomial σ R)} (h : SameBase F G)
    (hzero : F.map MvPolynomial.constantCoeff = G.map MvPolynomial.constantCoeff) :
    F = G := by
  have hu : IsUnit (comparison F G) := (comparisonUnit h).isUnit
  obtain ⟨r, _, hr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  have heval : MvPolynomial.constantCoeff (comparison F G) = 1 := by
    rw [← comparison_map, hzero, comparison_self]
  have hr1 : r = 1 := by simpa only [hr, MvPolynomial.constantCoeff_C] using heval
  apply eq_of_comparison_eq_one h
  simpa only [hr1, map_one] using hr

end FrameLift
end StableCoordinate

end OAI
