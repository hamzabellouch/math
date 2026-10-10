import OAI.Geometry.NodalSets.Coefficients.OriginalCoefficientComparison
import OAI.Geometry.NodalSets.Elliptic.AmbientMatrixForm

namespace OAI

namespace Yau.Target
open Matrix
noncomputable section

def ambientFormMatrix (B : AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ := fun i j ↦
  B (EuclideanSpace.basisFun (Fin 5) ℝ i) (EuclideanSpace.basisFun (Fin 5) ℝ j)

lemma ambientFormMatrix_form (B : AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ)
    (v w : AmbientBase) : ambientMatrixForm (ambientFormMatrix B) v w = B v w := by
  have hv := (EuclideanSpace.basisFun (Fin 5) ℝ).sum_repr v
  have hw := (EuclideanSpace.basisFun (Fin 5) ℝ).sum_repr w
  conv_rhs => rw [← hv, ← hw]
  simp [ambientMatrixForm_apply, ambientFormMatrix, map_sum, map_smul, mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma ambientFormMatrix_posDef (B : AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, v ≠ 0 → 0 < B v v) :
    (ambientFormMatrix B).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [ambientFormMatrix, hs]
  · intro v hv
    have hn : WithLp.toLp 2 v ≠ (0 : AmbientBase) := by
      intro h
      apply hv
      exact congrArg WithLp.ofLp h
    simpa only [← ambientFormMatrix_form B, ambientMatrixForm_dot, star_trivial] using
      hp (WithLp.toLp 2 v) hn

end
end Yau.Target

end OAI
