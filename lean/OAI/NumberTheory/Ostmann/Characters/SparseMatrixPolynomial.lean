import OAI.NumberTheory.Ostmann.Characters.SparseResidueMatrix

namespace OAI

/-! # The bilinear polynomial of a local sparse residue matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Four evaluations recover the four bilinear coefficients exactly. -/
theorem sparseResidueMatrix_polynomial {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (u v : ℂ) (x y : Option (ZMod p)) :
    sparseResidueMatrix S E u v x y =
      sparseResidueMatrix S E 0 0 x y +
      u * (sparseResidueMatrix S E 1 0 x y - sparseResidueMatrix S E 0 0 x y) +
      v * (sparseResidueMatrix S E 0 1 x y - sparseResidueMatrix S E 0 0 x y) +
      u * v * (sparseResidueMatrix S E 1 1 x y - sparseResidueMatrix S E 1 0 x y -
        sparseResidueMatrix S E 0 1 x y + sparseResidueMatrix S E 0 0 x y) := by
  cases x <;> cases y <;>
    simp only [sparseResidueMatrix, finiteBlockMatrix, polydiscLowerLinearMap_apply,
      polydiscSparseScalar, polydiscSparseSide, polydiscSparseLower, map_add, map_mul,
      starRingEnd_apply, star_star, map_one, map_zero] <;> ring

end Ostmann

end OAI
