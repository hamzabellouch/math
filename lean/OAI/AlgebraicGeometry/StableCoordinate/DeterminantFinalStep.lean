import OAI.AlgebraicGeometry.StableCoordinate.DeterminantRigidity
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantGradedObstruction

namespace OAI

/-!
# The final elementary step of determinant rigidity

A derivation which fixes the three polynomial base generators is determined
by a single coefficient.  Preservation of the actual fiber grading makes that
coefficient have weight `-2`.  If it lies in the polynomial base, whose weights
are nonnegative, it vanishes; so does the derivation.  The coefficient's
polynomiality is supplied separately by the locally nilpotent chart argument.
-/

namespace StableCoordinate.DeterminantRing

variable (k : Type*) [CommRing k]

/-- The actual weight obstruction annihilates every vertical derivation whose
coefficient is polynomial in the base variables. -/
theorem derivation_eq_zero_of_fixed_base_and_coefficient_mem
    (D : Derivation k (C k) (C k))
    (ha : D (a k) = 0) (hd : D (d k) = 0) (hu : D (u k) = 0)
    (hgraded : ∀ n : ℤ, ∀ x ∈ Obstruction.fiberPiece k n,
      D x ∈ Obstruction.fiberPiece k n)
    (hq : rigidityCoefficient D (b k) (c k) ∈ (baseMap (k := k)).range) :
    D = 0 := by
  have hb : b k ∈ Obstruction.fiberPiece k (-1) := by
    change Obstruction.cX k 2 ∈ Obstruction.fiberPiece k (-1)
    simpa [Obstruction.fiberWeight] using Obstruction.cX_mem_fiberPiece k 2
  have hc : c k ∈ Obstruction.fiberPiece k (-1) := by
    change Obstruction.cX k 3 ∈ Obstruction.fiberPiece k (-1)
    simpa [Obstruction.fiberWeight] using Obstruction.cX_mem_fiberPiece k 3
  have hzero : rigidityCoefficient D (b k) (c k) = 0 :=
    DeterminantGradedObstruction.coefficient_eq_zero_of_mem_baseRange k
      (hgraded (-1) (b k) hb) (hgraded (-1) (c k) hc) hq
  obtain ⟨hb', hc'⟩ := derivation_rigidityCoefficient D (a k) (d k) (b k) (c k)
    (determinant_relation k) ha hd
  rw [hzero, mul_zero] at hb' hc'
  exact derivation_eq_zero k D ha hd hb' hc' hu

end StableCoordinate.DeterminantRing

end OAI
