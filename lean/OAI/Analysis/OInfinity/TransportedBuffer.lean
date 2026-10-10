import OAI.Analysis.OInfinity.BufferAnchor
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! # Transporting the explicit absorption anchor

The canonical Fock split transports its corner by a connected unitary,
but transports its complementary isometry by left multiplication.  This
asymmetric transport still preserves connectedness of the absorption
anchor: its anchor is conjugate to a value of the original rotation path.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

namespace BufferAbsorptionCorner

/-- Corner coefficients are conjugated, whereas the complementary
isometry is moved by left multiplication, as in the finite Fock split. -/
def transported (D : BufferAbsorptionCorner E) (u : unitary E) : BufferAbsorptionCorner E := by
  let F := Unitary.conjStarAlgAut ℂ E u
  refine {
    q := F D.q
    w := (u : E) * D.w
    a := F D.a
    b := F D.b
    projection := isStarProjection_iff'.mpr ⟨?_, ?_⟩
    w_gram := ?_
    w_range := ?_
    w_orthogonal := ?_
    a_gram := ?_
    b_gram := ?_
    orthogonal := ?_
    ranges := ?_
  }
  · rw [← map_mul, D.projection.isIdempotentElem.eq]
  · rw [← map_star, D.projection.isSelfAdjoint.star_eq]
  · rw [star_mul]
    calc
      _ = star D.w * (star (u : E) * (u : E)) * D.w := by noncomm_ring
      _ = 1 := by rw [Unitary.star_mul_self_of_mem u.property, mul_one, D.w_gram]
  · calc
      _ = (u : E) * (D.w * star D.w) * star (u : E) := by rw [star_mul]; noncomm_ring
      _ = F (1 - D.q) := by rw [D.w_range]; rfl
      _ = 1 - F D.q := by rw [map_sub, map_one]
  · change ((u : E) * D.q * star (u : E)) * ((u : E) * D.w) = 0
    calc
      _ = (u : E) * D.q * (star (u : E) * (u : E)) * D.w := by noncomm_ring
      _ = 0 := by rw [Unitary.star_mul_self_of_mem u.property, mul_one,
        mul_assoc, D.w_orthogonal, mul_zero]
  · rw [← map_star, ← map_mul, D.a_gram]
  · rw [← map_star, ← map_mul, D.b_gram]
  · rw [← map_star, ← map_mul, D.orthogonal, map_zero]
  · rw [← map_star, ← map_star, ← map_mul, ← map_mul, ← map_add, D.ranges]

lemma transported_q (D : BufferAbsorptionCorner E) (u : unitary E) :
    (D.transported u).q = (u : E) * D.q * star (u : E) := rfl

lemma transported_w (D : BufferAbsorptionCorner E) (u : unitary E) :
    (D.transported u).w = (u : E) * D.w := rfl

lemma transported_a (D : BufferAbsorptionCorner E) (u : unitary E) :
    (D.transported u).a = (u : E) * D.a * star (u : E) := rfl

lemma transported_b (D : BufferAbsorptionCorner E) (u : unitary E) :
    (D.transported u).b = (u : E) * D.b * star (u : E) := rfl

/-- Exact asymmetric transport identity for the anchor. -/
lemma transported_anchor (D : BufferAbsorptionCorner E) (u : unitary E) :
    (D.transported u).anchor = u * D.rotation u * star u := by
  apply Subtype.ext
  change star ((u : E) * D.a * star (u : E)) +
      ((u : E) * D.w) * 1 *
        (star ((u : E) * D.b * star (u : E)) +
          (1 - (u : E) * D.q * star (u : E))) =
    ((u : E) * (star D.a + D.w * (u : E) * (star D.b + (1 - D.q)))) * star (u : E)
  simp only [star_mul, star_star, mul_one]
  calc
    _ = (u : E) * star D.a * star (u : E) +
        (u : E) * D.w * (u : E) * star D.b * star (u : E) +
        (u : E) * D.w - (u : E) * D.w * (u : E) * D.q * star (u : E) := by
      noncomm_ring
    _ = (u : E) * star D.a * star (u : E) +
        (u : E) * D.w * (u : E) * star D.b * star (u : E) +
        (u : E) * D.w * ((u : E) * star (u : E)) -
        (u : E) * D.w * (u : E) * D.q * star (u : E) := by
      rw [Unitary.mul_star_self_of_mem u.property, mul_one]
    _ = _ := by noncomm_ring

/-- The anchor remains connected for the actual transported Fock corner;
no path in a corner stabilizer is inferred from an ambient endpoint. -/
lemma transported_anchor_joined (D : BufferAbsorptionCorner E) (u : unitary E)
    (hD : Joined (1 : unitary E) D.anchor) (hu : Joined (1 : unitary E) u) :
    Joined (1 : unitary E) (D.transported u).anchor := by
  have hrot : Joined (1 : unitary E) (D.rotation u) := by
    have h := (hD.trans (D.absorption_joined_anchor u hu)).mul hu
    have he : D.absorption u * u = D.rotation u := by
      apply Subtype.ext
      change ((D.rotation u : E) * star (u : E)) * (u : E) = (D.rotation u : E)
      rw [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one]
    simpa only [one_mul, he] using h
  have hus : Joined (1 : unitary E) (star u) := by
    simpa only [star_one] using
      hu.map (continuous_star : Continuous (star : unitary E → unitary E))
  simpa only [one_mul, D.transported_anchor u] using (hu.mul hrot).mul hus

end BufferAbsorptionCorner

end WeakPureInfiniteness

end

end OAI
