import OAI.AlgebraicGeometry.StableCoordinate.FrameLiftUniqueness
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Lifting a quadric point to a determinant-one frame over a GCD domain

This is an algebraic substitute for the local trivialization step in the
additive-action lift.  It constructs a frame, rather than assuming a line
bundle is trivial.  After pullback to the factorial ring of the determinant-one
quadric, it can be applied over that ring's polynomial extension.
-/

noncomputable section

namespace StableCoordinate.QuadricFactorization

variable {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]

/-- Every point of `xy=z(z+1)` over a GCD domain with nonzero `x` admits a
factorization by a determinant-one matrix.  No Bezout-domain assumption is used. -/
theorem exists_frame_of_ne_zero (x y z : R) (hx : x ≠ 0)
    (h : x * y = z * (z + 1)) :
    ∃ a d b c : R,
      a * b = x ∧ d * b = z ∧ d * c = y ∧ a * c = z + 1 ∧
        a * c - b * d = 1 := by
  rcases (inferInstance : IsGCDMonoid R) with ⟨hGCD⟩
  let := hGCD
  obtain ⟨a, d, hxa, hzd, had⟩ := extract_gcd x z
  let b := gcd x z
  have hb : b ≠ 0 := by
    intro hb
    exact hx (by simpa [b, hb] using hxa)
  have ha : a ≠ 0 := by
    intro ha
    exact hx (by simpa [ha] using hxa)
  have hrel : IsRelPrime a d := gcd_isUnit_iff_isRelPrime.mp had
  have hcancel : a * y = d * (z + 1) := by
    apply mul_left_cancel₀ hb
    calc
      b * (a * y) = x * y := by rw [hxa]; simp [b, mul_assoc]
      _ = z * (z + 1) := h
      _ = b * (d * (z + 1)) := by rw [hzd]; simp [b, mul_assoc]
  have hadvd : a ∣ d * (z + 1) := ⟨y, hcancel.symm⟩
  obtain ⟨c, hc⟩ := hrel.dvd_of_dvd_mul_left hadvd
  have hy : d * c = y := by
    apply mul_left_cancel₀ ha
    calc
      a * (d * c) = d * (a * c) := by ring
      _ = d * (z + 1) := by rw [← hc]
      _ = a * y := hcancel.symm
  refine ⟨a, d, b, c, ?_, ?_, hy, hc.symm, ?_⟩
  · simpa [b, mul_comm] using hxa.symm
  · simpa [b, mul_comm] using hzd.symm
  · rw [← hc, ← hzd]
    ring

/-- The zero-`x` cases are elementary, so a determinant frame exists without
any nonvanishing assumption on the given quadric point. -/
theorem exists_frame (x y z : R) (h : x * y = z * (z + 1)) :
    ∃ a d b c : R,
      a * b = x ∧ d * b = z ∧ d * c = y ∧ a * c = z + 1 ∧
        a * c - b * d = 1 := by
  by_cases hx : x = 0
  · have hz : z = 0 ∨ z + 1 = 0 := mul_eq_zero.mp (by rw [← h, hx, zero_mul])
    rcases hz with hz | hz
    · refine ⟨1, y, 0, 1, ?_⟩
      simp [hx, hz]
    · have hz' : z = -1 := eq_neg_of_add_eq_zero_left hz
      refine ⟨0, 1, -1, y, ?_⟩
      simp [hx, hz']
  · exact exists_frame_of_ne_zero x y z hx h

/-- Existence in the canonical frame type used by the action-lift construction. -/
theorem exists_frameAbove (x y z : R) (h : x * y = z * (z + 1)) :
    ∃ F : FrameLift.Frame R,
      F.a * F.b = x ∧ F.d * F.c = y ∧ F.d * F.b = z := by
  obtain ⟨a, d, b, c, hx, hz, hy, _, hdet⟩ := exists_frame x y z h
  exact ⟨⟨a, d, b, c, hdet⟩, hx, hy, hz⟩

/-- A choice of determinant-one frame above a quadric point. -/
def frameAbove (x y z : R) (h : x * y = z * (z + 1)) : FrameLift.Frame R :=
  (exists_frameAbove x y z h).choose

@[simp]
theorem frameAbove_ab (x y z : R) (h : x * y = z * (z + 1)) :
    (frameAbove x y z h).a * (frameAbove x y z h).b = x :=
  (exists_frameAbove x y z h).choose_spec.1

@[simp]
theorem frameAbove_dc (x y z : R) (h : x * y = z * (z + 1)) :
    (frameAbove x y z h).d * (frameAbove x y z h).c = y :=
  (exists_frameAbove x y z h).choose_spec.2.1

@[simp]
theorem frameAbove_db (x y z : R) (h : x * y = z * (z + 1)) :
    (frameAbove x y z h).d * (frameAbove x y z h).b = z :=
  (exists_frameAbove x y z h).choose_spec.2.2

end StableCoordinate.QuadricFactorization

end

end OAI
