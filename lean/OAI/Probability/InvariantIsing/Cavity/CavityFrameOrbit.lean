import OAI.Probability.InvariantIsing.Cavity.CavityFrameTransitive
import OAI.Probability.InvariantIsing.Haar.MatrixRotation

namespace OAI

/-! Matrix form of transitivity and continuity of the frame orbit action. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

def cavityRotationMatrix {n : ℕ} (U : Rotation n) : Orthogonal n :=
  ⟨U.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    U.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin n) ℝ)
      (EuclideanSpace.basisFun (Fin n) ℝ)⟩

lemma cavityRotationMatrix_apply {n : ℕ} (U : Rotation n)
    (x : EuclideanSpace ℝ (Fin n)) : matrixRotation (cavityRotationMatrix U) x = U x := by
  have h := U.toLinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis x
  ext i
  exact congrFun h i

lemma cavity_orthonormal_of_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) :
    Orthonormal ℝ (fun j : Fin q =>
      (WithLp.toLp 2 (fun i : Fin n => A i j) : EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrArg (fun B : Matrix (Fin q) (Fin q) ℝ => B i j) hA
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using h

theorem cavityFrame_transitive {n q : ℕ} (A B : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) (hB : B.transpose * B = 1) :
    ∃ U : Orthogonal n, (U : Matrix (Fin n) (Fin n) ℝ) * A = B := by
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive _ _
    (cavity_orthonormal_of_gram A hA) (cavity_orthonormal_of_gram B hB)
  refine ⟨cavityRotationMatrix U, ?_⟩
  ext i j
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) (hU j)
  rw [← cavityRotationMatrix_apply U] at h
  exact h

lemma continuous_cavityFrameAction (n q : ℕ) :
    Continuous (fun p : Orthogonal n × Matrix (Fin n) (Fin q) ℝ =>
      (p.1 : Matrix (Fin n) (Fin n) ℝ) * p.2) := by
  exact (continuous_subtype_val.comp continuous_fst).matrix_mul continuous_snd

end InvariantIsing

end

end OAI
