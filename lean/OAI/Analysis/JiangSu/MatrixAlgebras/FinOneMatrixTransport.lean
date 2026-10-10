import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CornerRanks
import OAI.Analysis.JiangSu.MatrixAlgebras.CornerCompression

namespace OAI


noncomputable section
namespace Pureness
open TraceCone

variable {A : Type*} [CStarAlgebra A]

lemma scalarMatrixHom_finOne_bijective [PartialOrder A] [StarOrderedRing A] :
    Function.Bijective (scalarMatrixHom (ι := Fin 1) (A := A)) := by
  constructor
  · intro a b h
    have he := congrArg (fun M : FinMatrix A 1 => M 0 0) h
    exact he
  · intro M
    refine ⟨M 0 0,?_⟩
    apply CStarMatrix.ext
    intro i j
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst i; subst j
    rfl

variable [PartialOrder A] [StarOrderedRing A]

def scalarFinOneEquiv : A ≃⋆ₐ[ℂ] FinMatrix A 1 :=
  StarAlgEquiv.ofBijective (scalarMatrixHom (ι := Fin 1)) scalarMatrixHom_finOne_bijective

lemma scalarFinOneEquiv_apply (a : A) :
    scalarFinOneEquiv a = scalarMatrixHom (ι := Fin 1) a := rfl

lemma scalarFinOneEquiv_symm_apply (M : FinMatrix A 1) :
    scalarFinOneEquiv.symm M = M 0 0 := by
  obtain ⟨a,rfl⟩ := scalarMatrixHom_finOne_bijective.2 M
  change scalarFinOneEquiv.symm (scalarFinOneEquiv a) = _
  rw [StarAlgEquiv.symm_apply_apply]
  rfl

end Pureness


namespace Pureness
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {k l : ℕ}

lemma compress_nonneg (h : k ≤ l) (a : MatrixStage A l) (ha : 0 ≤ a) : 0 ≤ compress h a := by
  apply (nonUnitalStarAlgHom_nonneg_iff (cornerHom h) (corner_injective h) _).mp
  change 0 ≤ corner h (compress h a)
  rw [corner_compress]
  simpa only [cornerProjection_star] using star_left_conjugate_nonneg ha (cornerProjection (A := A) h)

lemma matrixRank_compress_le [NeZero k] [NeZero l] (τ : TracialState A) (h : k ≤ l)
    (a : MatrixStage A l) (ha : 0 ≤ a) : matrixRank τ (compress h a) ≤ matrixRank τ a := by
  rw [← matrixRank_corner τ h _ (compress_nonneg h a ha)]
  unfold matrixRank
  gcongr
  exact (corner_compress_cuntz h a).rank_le
    (corner_nonneg h _ (compress_nonneg h a ha)) ha (matrixTracialState τ)

lemma completedCompression_rank_monotone (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Monotone (fun k : ℕ => matrixRank τ (completedCompress A (k + 1) a)) := by
  intro k l h
  dsimp only
  rw [← completedCompress_compat (Nat.add_le_add_right h 1) a]
  exact matrixRank_compress_le τ _ _ (completedCompress_nonneg _ a ha)

end Pureness
end

end OAI
