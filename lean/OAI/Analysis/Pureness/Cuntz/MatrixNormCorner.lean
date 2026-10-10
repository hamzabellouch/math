import OAI.Analysis.Pureness.Completion.CStarNormNonUnitalPullback
import OAI.Analysis.Pureness.Completion.CStarNormBoundEquality
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace OAI
noncomputable section
namespace CuntzPureness
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def algebraicMatrixCorner (o : ι) : R →⋆ₙₐ[ℂ] Matrix ι ι R where
  __ := Matrix.singleLinearMap ℂ o o
  map_zero' := Matrix.single_zero o o
  map_mul' a b := (Matrix.single_mul_single_same a o o o b).symm
  map_star' a := by
    change Matrix.single o o (star a) = (Matrix.single o o a).conjTranspose
    simp

omit [StarModule ℂ R] in
lemma algebraicMatrixCorner_injective (o : ι) :
    Function.Injective (algebraicMatrixCorner (R := R) o) := by
  intro a b h
  have he := congrArg (fun M : Matrix ι ι R => M o o) h
  change Matrix.single o o a o o = Matrix.single o o b o o at he
  simpa only [Matrix.single_apply_same] using he

theorem matrixNorm_bound_of_corner_eq (o : ι)
    (p q : CStarAlgebraNorm (Matrix ι ι R))
    (hcorner : ∀ a : R, p.toAlgebraNorm (Matrix.single o o a) =
      q.toAlgebraNorm (Matrix.single o o a)) :
    ∃ C : ℝ, ∀ M, p.toAlgebraNorm M ≤ C*q.toAlgebraNorm M := by
  let u (i j : ι) : Matrix ι ι R := Matrix.single i j 1
  let C (i j : ι) : ℝ :=
    p.toAlgebraNorm (u i o) * q.toAlgebraNorm (u o i) *
      q.toAlgebraNorm (u j o) * p.toAlgebraNorm (u o j)
  refine ⟨∑ i, ∑ j, C i j, fun M => ?_⟩
  have hentry (i j : ι) :
      p.toAlgebraNorm (Matrix.single i j (M i j)) ≤ C i j*q.toAlgebraNorm M := by
    have h₁ : u i o * Matrix.single o o (M i j) * u o j = Matrix.single i j (M i j) := by
      simp [u]
    have h₂ : u o i*M*u j o = Matrix.single o o (M i j) := by simp [u]
    calc
      _ ≤ p.toAlgebraNorm (u i o)*p.toAlgebraNorm (Matrix.single o o (M i j))*
          p.toAlgebraNorm (u o j) := by
        rw [← h₁]
        exact (map_mul_le_mul _ _ _).trans
          (mul_le_mul_of_nonneg_right (map_mul_le_mul _ _ _) (apply_nonneg _ _))
      _ = p.toAlgebraNorm (u i o)*q.toAlgebraNorm (Matrix.single o o (M i j))*
          p.toAlgebraNorm (u o j) := by rw [hcorner]
      _ ≤ p.toAlgebraNorm (u i o)*(q.toAlgebraNorm (u o i)*q.toAlgebraNorm M*
          q.toAlgebraNorm (u j o))*p.toAlgebraNorm (u o j) := by
        gcongr
        rw [← h₂]
        exact (map_mul_le_mul _ _ _).trans
          (mul_le_mul_of_nonneg_right (map_mul_le_mul _ _ _) (apply_nonneg _ _))
      _ = C i j*q.toAlgebraNorm M := by dsimp [C]; ring
  calc
    p.toAlgebraNorm M = ‖p.completionMap (∑ i, ∑ j, Matrix.single i j (M i j))‖ := by
      rw [Matrix.sum_sum_single M, p.completionMap_norm]
      rfl
    _ ≤ ∑ i, ∑ j, p.toAlgebraNorm (Matrix.single i j (M i j)) := by
      simp only [map_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
        (norm_sum_le _ _).trans_eq (by simp only [p.completionMap_norm]))
    _ ≤ ∑ i, ∑ j, C i j*q.toAlgebraNorm M :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = (∑ i, ∑ j, C i j)*q.toAlgebraNorm M := by simp only [Finset.sum_mul]

theorem matrixNorm_eq_of_corner_eq (o : ι)
    (p q : CStarAlgebraNorm (Matrix ι ι R))
    (hcorner : ∀ a : R, p.toAlgebraNorm (Matrix.single o o a) =
      q.toAlgebraNorm (Matrix.single o o a)) : p=q :=
  CStarAlgebraNorm.eq_of_mutual_bound p q
    (matrixNorm_bound_of_corner_eq o p q hcorner)
    (matrixNorm_bound_of_corner_eq o q p fun a => (hcorner a).symm)
end CuntzPureness

end

end OAI
