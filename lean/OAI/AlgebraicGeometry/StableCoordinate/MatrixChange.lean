import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace OAI

/-!
# The determinant-preserving change in §2

These identities are valid in every commutative ring.  The parameter `t` gives
`(I - 2t n eᵀ) M`, and composition adds parameters.  No division by two is
needed in the coordinate formulas.
-/

namespace StableCoordinate.MatrixChange

variable {K : Type*} [CommRing K]

/-- The negative determinant of the displayed two-by-two matrix. -/
def quad (p s u F : K) : K := s ^ 2 - u ^ 2 + p * F

def pChange (t p s u F J : K) : K :=
  p + 2 * t * quad p s u F * (quad p s u F * (s - u) + p * J)

def sChange (t p s u F J : K) : K :=
  s + t * (2 * J * quad p s u F * u - p * J ^ 2 - (quad p s u F) ^ 2 * F)

def uChange (t p s u F J : K) : K :=
  u + t * (2 * s * J * quad p s u F + p * J ^ 2 - (quad p s u F) ^ 2 * F)

def FChange (t p s u F J : K) : K :=
  F + 2 * t * J * (J * (s + u) - quad p s u F * F)

/-- The defining equation of the five-variable hypersurface. -/
def relation (p s u F J : K) : K :=
  (quad p s u F) ^ 2 * F - (1 + 2 * s * quad p s u F) * J - p * J ^ 2 - u

section Maps
variable {L : Type*} [CommRing L] {G : Type*} [FunLike G K L] [RingHomClass G K L]

@[simp] lemma map_quad (h : G) (p s u F : K) :
    h (quad p s u F) = quad (h p) (h s) (h u) (h F) := by
  simp [quad]

@[simp] lemma map_pChange (h : G) (t p s u F J : K) :
    h (pChange t p s u F J) = pChange (h t) (h p) (h s) (h u) (h F) (h J) := by
  simp [pChange, map_ofNat]

@[simp] lemma map_sChange (h : G) (t p s u F J : K) :
    h (sChange t p s u F J) = sChange (h t) (h p) (h s) (h u) (h F) (h J) := by
  simp [sChange, map_ofNat]

@[simp] lemma map_uChange (h : G) (t p s u F J : K) :
    h (uChange t p s u F J) = uChange (h t) (h p) (h s) (h u) (h F) (h J) := by
  simp [uChange, map_ofNat]

@[simp] lemma map_FChange (h : G) (t p s u F J : K) :
    h (FChange t p s u F J) = FChange (h t) (h p) (h s) (h u) (h F) (h J) := by
  simp [FChange, map_ofNat]

@[simp] lemma map_relation (h : G) (p s u F J : K) :
    h (relation p s u F J) = relation (h p) (h s) (h u) (h F) (h J) := by
  simp [relation, map_ofNat]

end Maps

lemma quad_change (t p s u F J : K) :
    quad (pChange t p s u F J) (sChange t p s u F J)
      (uChange t p s u F J) (FChange t p s u F J) = quad p s u F := by
  unfold quad pChange sChange uChange FChange
  ring

lemma pChange_add (t r p s u F J : K) :
    pChange t (pChange r p s u F J) (sChange r p s u F J)
      (uChange r p s u F J) (FChange r p s u F J) J = pChange (t + r) p s u F J := by
  rw [pChange]
  simp only [quad_change]
  simp only [pChange, sChange, uChange]
  ring

lemma sChange_add (t r p s u F J : K) :
    sChange t (pChange r p s u F J) (sChange r p s u F J)
      (uChange r p s u F J) (FChange r p s u F J) J = sChange (t + r) p s u F J := by
  rw [sChange]
  simp only [quad_change]
  simp only [pChange, sChange, uChange, FChange]
  ring

lemma uChange_add (t r p s u F J : K) :
    uChange t (pChange r p s u F J) (sChange r p s u F J)
      (uChange r p s u F J) (FChange r p s u F J) J = uChange (t + r) p s u F J := by
  rw [uChange]
  simp only [quad_change]
  simp only [pChange, sChange, uChange, FChange]
  ring

lemma FChange_add (t r p s u F J : K) :
    FChange t (pChange r p s u F J) (sChange r p s u F J)
      (uChange r p s u F J) (FChange r p s u F J) J = FChange (t + r) p s u F J := by
  rw [FChange]
  simp only [quad_change]
  simp only [sChange, uChange, FChange]
  ring

@[simp] lemma pChange_zero (p s u F J : K) : pChange 0 p s u F J = p := by
  simp [pChange]
@[simp] lemma sChange_zero (p s u F J : K) : sChange 0 p s u F J = s := by
  simp [sChange]
@[simp] lemma uChange_zero (p s u F J : K) : uChange 0 p s u F J = u := by
  simp [uChange]
@[simp] lemma FChange_zero (p s u F J : K) : FChange 0 p s u F J = F := by
  simp [FChange]

lemma uChange_one (p s u F J : K) :
    uChange 1 p s u F J = -relation p s u F J - J := by
  unfold uChange relation
  ring

lemma relation_change_neg_one (p s u F J : K) :
    relation (pChange (-1) p s u F J) (sChange (-1) p s u F J)
      (uChange (-1) p s u F J) (FChange (-1) p s u F J) J = -J - u := by
  have h := uChange_one (pChange (-1) p s u F J) (sChange (-1) p s u F J)
      (uChange (-1) p s u F J) (FChange (-1) p s u F J) J
  rw [uChange_add] at h
  simp only [add_neg_cancel, uChange_zero] at h
  linear_combination h

end StableCoordinate.MatrixChange

end OAI
