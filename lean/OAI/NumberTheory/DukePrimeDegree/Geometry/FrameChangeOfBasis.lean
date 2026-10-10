import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedFrame
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

/-!
# Deriving the frame cocycle from subspace transport

Two full-rank finite frames with the same column space differ by an
invertible matrix. This supplies the change of basis in the diagonal
recurrence argument from transport of the actual velocity subspaces.
-/

noncomputable section
open Matrix Set
open scoped BigOperators

namespace DukePrimeDegree

theorem exists_invertible_frame_change {n k : ℕ}
    (B C : Matrix (Fin n) (Fin k) ℝ)
    (hC : LinearIndependent ℝ C.col)
    (hspan : Submodule.span ℝ (Set.range C.col) ≤
      Submodule.span ℝ (Set.range B.col)) :
    ∃ R : Matrix (Fin k) (Fin k) ℝ, R.det ≠ 0 ∧ C = B * R := by
  have hcol (j : Fin k) : ∃ c : Fin k → ℝ, B *ᵥ c = C.col j := by
    have hj : C.col j ∈ LinearMap.range B.mulVecLin := by
      rw [Matrix.range_mulVecLin]
      exact hspan (Submodule.subset_span ⟨j, rfl⟩)
    exact hj
  choose c hc using hcol
  let R : Matrix (Fin k) (Fin k) ℝ := fun i j => c j i
  have hBR : C = B * R := by
    ext i j
    exact (congrFun (hc j) i).symm
  have hRinj : Function.Injective R.mulVec := by
    intro u v huv
    apply (Matrix.mulVec_injective_iff.mpr hC)
    rw [hBR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huv]
  refine ⟨R, ?_, hBR⟩
  exact ((Matrix.isUnit_iff_isUnit_det R).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hRinj)).ne_zero

theorem linearIndependent_frame_of_minor {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (p : Fin k ↪ Fin n)
    (hp : frameMinor B p ≠ 0) : LinearIndependent ℝ B.col := by
  apply Matrix.mulVec_injective_iff.mp
  intro u v huv
  apply Matrix.mulVec_injective_of_det_ne_zero hp
  ext i
  exact congrFun huv (p i)

end DukePrimeDegree

end

end OAI
