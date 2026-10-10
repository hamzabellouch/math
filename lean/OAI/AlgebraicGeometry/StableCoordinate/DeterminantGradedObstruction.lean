import OAI.AlgebraicGeometry.StableCoordinate.DeterminantWeights
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantGradings

namespace OAI

/-!
# Final weight obstruction in the constructed determinant grading

This module connects the actual quotient grading to the Laurent proof of
negative-weight vanishing.  The two independently defined quotient-ring
interfaces are definitionally equal; no extra grading or injectivity
hypothesis is imposed here.
-/

namespace StableCoordinate
namespace DeterminantGradedObstruction

open DeterminantRing

variable (k : Type*) [CommRing k]

/-- A fiber-weight identity for the actual Laurent coaction is equivalent
to membership in the constructed graded piece.  This also gives the
converse needed after differentiating an equivariant additive action. -/
theorem mem_fiberPiece_iff_fiberCoaction {q : C k} (n : ℤ) :
    q ∈ Obstruction.fiberPiece k n ↔
      DeterminantWeights.fiberCoaction k q = AddMonoidAlgebra.single n q :=
  HomogeneousQuotientWeight.mem_piece_iff_coaction Obstruction.fiberWeight
    (relation k) (DeterminantWeights.relation_fiber_homogeneous k) n q

/-- An element of the actual fiber-weight piece of negative degree cannot
lie nontrivially in the polynomial subalgebra `k[a,d,u]`. -/
theorem eq_zero_of_mem_baseRange_of_mem_fiberPiece {q : C k}
    (hq : q ∈ (baseMap (k := k)).range) {n : ℤ} (hn : n < 0)
    (hg : q ∈ Obstruction.fiberPiece k n) : q = 0 :=
  DeterminantWeights.eq_zero_of_mem_baseRange_of_mem_homogeneous_piece k hq hn hg

/-- A source-style weight-preserving derivation has coefficient
`c*D(b)-b*D(c)` in fiber degree `-2`. -/
theorem coefficient_mem_fiberPiece_neg_two {r s : C k}
    (hr : r ∈ Obstruction.fiberPiece k (-1))
    (hs : s ∈ Obstruction.fiberPiece k (-1)) :
    c k * r - b k * s ∈ Obstruction.fiberPiece k (-2) := by
  have hc : c k ∈ Obstruction.fiberPiece k (-1) := by
    change Obstruction.cX k 3 ∈ Obstruction.fiberPiece k (-1)
    simpa [Obstruction.fiberWeight] using Obstruction.cX_mem_fiberPiece k 3
  have hb : b k ∈ Obstruction.fiberPiece k (-1) := by
    change Obstruction.cX k 2 ∈ Obstruction.fiberPiece k (-1)
    simpa [Obstruction.fiberWeight] using Obstruction.cX_mem_fiberPiece k 2
  have hcr : c k * r ∈ Obstruction.fiberPiece k (-2) := by
    exact SetLike.mul_mem_graded (R := Obstruction.C k) hc hr
  have hbs : b k * s ∈ Obstruction.fiberPiece k (-2) := by
    exact SetLike.mul_mem_graded (R := Obstruction.C k) hb hs
  exact (Obstruction.fiberPiece k (-2)).sub_mem hcr hbs

/-- The precise contradiction endpoint for the rigidity coefficient,
without introducing a homogeneous-polynomial representative premise. -/
theorem coefficient_eq_zero_of_mem_baseRange
    {r s : C k} (hr : r ∈ Obstruction.fiberPiece k (-1))
    (hs : s ∈ Obstruction.fiberPiece k (-1))
    (hq : c k * r - b k * s ∈ (baseMap (k := k)).range) :
    c k * r - b k * s = 0 := by
  exact eq_zero_of_mem_baseRange_of_mem_fiberPiece k hq (by norm_num)
    (coefficient_mem_fiberPiece_neg_two k hr hs)

end DeterminantGradedObstruction
end StableCoordinate

end OAI
