import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateLieBrackets

namespace OAI

/-! # Finite-coordinate expansion of the transported Lie bracket -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- A single elementary coordinate bilinear map. -/
def coordinateBilinearUnit {n : ℕ} (i j k : Fin n) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.proj i).smulRight
    ((ContinuousLinearMap.proj j).smulRight (Pi.single k (1 : ℝ)))

@[simp] theorem coordinateBilinearUnit_apply {n : ℕ} (i j k : Fin n)
    (x y : Fin n → ℝ) :
    coordinateBilinearUnit i j k x y = x i • y j • Pi.single k (1 : ℝ) := rfl

/-- Every coordinate bracket is the finite linear combination of its
structure constants and elementary bilinear maps. -/
theorem basisBracket_eq_coordinate_sum
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
    (b : Basis (Fin n) ℝ L) :
    basisBracket b = ∑ i, ∑ j, ∑ k,
      b.repr ⁅b i, b j⁆ k • coordinateBilinearUnit i j k := by
  ext x y k
  rw [basisBracket_apply]
  change b.repr ⁅b.equivFun.symm x, b.equivFun.symm y⁆ k = _
  rw [basis_bracket_coordinate]
  simp only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp [Pi.smul_apply, Pi.single_apply, mul_comm, mul_assoc]

end PolycyclicRecognition

end

end OAI
