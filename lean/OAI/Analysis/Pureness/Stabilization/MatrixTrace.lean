import OAI.Analysis.Pureness.Stabilization.RankFunctorial
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace OAI
noncomputable section
open scoped NNReal ENNReal Topology CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι]
namespace Positive

lemma exists_starMul_factor (a : Positive A) : ∃ b : A, star b * b = a.1 := by
  refine ⟨CFC.sqrt a.1, ?_⟩
  rw [(CFC.sqrt_nonneg a.1).star_eq, CFC.sqrt_mul_sqrt_self a.1 a.2]

lemma matrix_diagonal_nonneg (a : Positive (CStarMatrix ι ι A)) (i : ι) : 0 ≤ a.1 i i := by
  obtain ⟨b, hb⟩ := exists_starMul_factor a
  rw [← hb, CStarMatrix.mul_apply]
  exact Finset.sum_nonneg fun j _ => by
    rw [CStarMatrix.star_apply]
    exact star_mul_self_nonneg _

def matrixDiagonal (a : Positive (CStarMatrix ι ι A)) (i : ι) : Positive A :=
  ⟨a.1 i i, matrix_diagonal_nonneg a i⟩

lemma matrixDiagonal_continuous (i : ι) :
    Continuous (fun a : Positive (CStarMatrix ι ι A) => matrixDiagonal a i) := by
  apply Continuous.subtype_mk
  change Continuous (fun a : Positive (CStarMatrix ι ι A) => a.1 i i)
  exact ((continuous_apply i).comp (continuous_apply i)).comp
    ((CStarMatrix.ofMatrixL (m := ι) (n := ι) (A := A)).symm.continuous.comp continuous_subtype_val)

lemma matrixDiagonal_zero (i : ι) :
    matrixDiagonal (Positive.zero : Positive (CStarMatrix ι ι A)) i = Positive.zero :=
  Subtype.ext rfl

lemma matrixDiagonal_add (a b : Positive (CStarMatrix ι ι A)) (i : ι) :
    matrixDiagonal (add a b) i = add (matrixDiagonal a i) (matrixDiagonal b i) :=
  Subtype.ext rfl

lemma matrixDiagonal_smul (s : ℝ≥0) (a : Positive (CStarMatrix ι ι A)) (i : ι) :
    matrixDiagonal (smul s a) i = smul s (matrixDiagonal a i) := Subtype.ext rfl

lemma matrixDiagonal_starMul (x : CStarMatrix ι ι A) (i : ι) :
    matrixDiagonal (starMul x) i = sum Finset.univ (fun j => starMul (x j i)) := by
  apply Subtype.ext
  simp [matrixDiagonal, starMul, sum, CStarMatrix.mul_apply, CStarMatrix.star_apply]

lemma matrixDiagonal_mulStar (x : CStarMatrix ι ι A) (i : ι) :
    matrixDiagonal (mulStar x) i = sum Finset.univ (fun j => mulStar (x i j)) := by
  apply Subtype.ext
  simp [matrixDiagonal, mulStar, sum, CStarMatrix.mul_apply, CStarMatrix.star_apply]

end Positive
namespace ExtendedTrace

def matrixTrace (τ : ExtendedTrace A) (ι : Type*) [Fintype ι] :
    ExtendedTrace (CStarMatrix ι ι A) where
  toFun a := ∑ i, τ (Positive.matrixDiagonal a i)
  map_zero := by simp [Positive.matrixDiagonal_zero, τ.map_zero]
  map_add a b := by simp only [Positive.matrixDiagonal_add, τ.map_add, Finset.sum_add_distrib]
  map_smul s a := by simp only [Positive.matrixDiagonal_smul, τ.map_smul, Finset.mul_sum]
  tracial x := by
    simp only [Positive.matrixDiagonal_starMul, Positive.matrixDiagonal_mulStar,
      τ.map_sum, τ.tracial]
    exact Finset.sum_comm
  lowerSemicontinuous := lowerSemicontinuous_sum (fun i _ =>
    τ.lowerSemicontinuous.comp (Positive.matrixDiagonal_continuous i))

@[simp] theorem matrixTrace_apply (τ : ExtendedTrace A) (a : Positive (CStarMatrix ι ι A)) :
    τ.matrixTrace ι a = ∑ i, τ (Positive.matrixDiagonal a i) := rfl

end ExtendedTrace
variable [DecidableEq ι]

def matrixCorner (i : ι) : A →⋆ₙₐ[ℂ] CStarMatrix ι ι A where
  toFun a := CStarMatrix.ofMatrix (Matrix.single i i a)
  map_zero' := by
    ext j k
    simp [Matrix.single]
  map_add' a b := by
    change Matrix.single i i (a + b) = Matrix.single i i a + Matrix.single i i b
    exact Matrix.single_add i i a b
  map_smul' s a := by
    ext j k
    by_cases hji : i = j <;> by_cases hki : i = k <;>
      simp [Matrix.single, hji, hki, CStarMatrix.smul_apply]
  map_mul' a b := by
    change Matrix.single i i (a * b) = Matrix.single i i a * Matrix.single i i b
    simp
  map_star' a := by
    change Matrix.single i i (star a) = (Matrix.single i i a).conjTranspose
    exact (Matrix.conjTranspose_single i i a).symm

namespace Positive

lemma matrixDiagonal_corner (i j : ι) (a : Positive A) :
    matrixDiagonal (map (matrixCorner i) a) j = if j = i then a else Positive.zero := by
  split_ifs with hj
  · subst j
    apply Subtype.ext
    simp [matrixDiagonal, map, matrixCorner]
  · apply Subtype.ext
    simp [matrixDiagonal, map, matrixCorner, Matrix.single, Ne.symm hj, Positive.zero]

end Positive
namespace ExtendedTrace

theorem matrixTrace_corner (τ : ExtendedTrace A) (i : ι) (a : Positive A) :
    τ.matrixTrace ι (Positive.map (matrixCorner i) a) = τ a := by
  rw [matrixTrace_apply]
  simp only [Positive.matrixDiagonal_corner]
  simp [apply_ite, τ.map_zero]

lemma matrixTrace_pullback_corner (τ : ExtendedTrace A) (i : ι) :
    (τ.matrixTrace ι).pullback (matrixCorner i) = τ := by
  ext a
  exact τ.matrixTrace_corner i a

theorem matrixRank_corner (τ : ExtendedTrace A) (i : ι) (a : Positive A) :
    (τ.matrixTrace ι).rank (Positive.map (matrixCorner i) a) = τ.rank a := by
  rw [← rank_pullback, matrixTrace_pullback_corner]

end ExtendedTrace

end CuntzTrace

end

end OAI
