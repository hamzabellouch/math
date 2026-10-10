import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularHeight

namespace OAI

/-! # Transporting a triangular adjoint basis through a Lie isomorphism -/

noncomputable section
namespace PolycyclicRecognition

variable {L K : Type*} [LieRing L] [LieAlgebra ℝ L]
  [LieRing K] [LieAlgebra ℝ K] {n : ℕ}

/-- The same adjoint matrices in the pulled-back basis. -/
def TriangularAdjoint.comapLieEquiv (T : TriangularAdjoint K n) (e : L ≃ₗ⁅ℝ⁆ K) :
    TriangularAdjoint L n where
  basis := T.basis.map e.toLinearEquiv.symm
  upper x := by
    have hm : LinearMap.toMatrix (T.basis.map e.toLinearEquiv.symm)
        (T.basis.map e.toLinearEquiv.symm) (LieAlgebra.ad ℝ L x) =
        LinearMap.toMatrix T.basis T.basis (LieAlgebra.ad ℝ K (e x)) := by
      ext i j
      simp only [LinearMap.toMatrix_apply]
      change T.basis.repr (e ⁅x,e.symm (T.basis j)⁆) i =
        T.basis.repr ⁅e x,T.basis j⁆ i
      rw [e.map_lie,e.apply_symm_apply]
    rw [hm]
    exact T.upper (e x)

theorem nonempty_triangularAdjoint_of_lieEquiv (e : L ≃ₗ⁅ℝ⁆ K)
    (h : ∃ m : ℕ, Nonempty (TriangularAdjoint K m)) :
    ∃ m : ℕ, Nonempty (TriangularAdjoint L m) := by
  obtain ⟨m, ⟨T⟩⟩ := h
  exact ⟨m, ⟨T.comapLieEquiv e⟩⟩

end PolycyclicRecognition

end

end OAI
