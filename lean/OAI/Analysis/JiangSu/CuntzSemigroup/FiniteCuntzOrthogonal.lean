import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionFunctions.FiniteSpectralIntegralOrthogonal

namespace OAI


noncomputable section
namespace Pureness
open TraceCone
open scoped CStarAlgebra

variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

private noncomputable abbrev positiveSqrt (a : Positive D) : D := CFC.sqrt a.1

private theorem positiveSqrt_star (a : Positive D) : star (positiveSqrt a) = positiveSqrt a :=
  (CFC.sqrt_nonneg a.1).star_eq

private theorem positiveSqrt_mul (a : Positive D) : positiveSqrt a * positiveSqrt a = a.1 :=
  CFC.sqrt_mul_sqrt_self a.1 a.2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finitePositiveClass_polar (n : ℕ) (x : FinMatrix A n) :
    finitePositiveClass n (Positive.starMul x) = finitePositiveClass n (Positive.mulStar x) := by
  apply le_antisymm
  · exact (finitePositiveClass_le_iff n _ _).mpr (star_mul_self_cuntzSubequiv x)
  · exact (finitePositiveClass_le_iff n _ _).mpr (mul_star_self_cuntzSubequiv x)

theorem finitePositiveClass_orthogonal_add (n : ℕ) (M N : Positive (FinMatrix A n))
    (hMN : M.1*N.1 = 0) :
    finitePositiveClass n (Positive.add M N) = finitePositiveClass n M + finitePositiveClass n N := by
  let e := CStarMatrix.reindexₐ ℂ A (finProdFinEquiv : (Fin n × Fin 2) ≃ Fin (n*2))
  let y := e (finiteOrthogonalColumn n (positiveSqrt M) (positiveSqrt N))
  have hcross := positive_sqrt_mul_zero M N hMN
  have hcross' : positiveSqrt N * positiveSqrt M = 0 := by
    simpa only [star_mul,positiveSqrt_star M,positiveSqrt_star N,star_zero] using congrArg star hcross
  have hl : Positive.starMul y = Positive.map (matrixInterleave n) (positiveProduct (Positive.add M N) Positive.zero) := by
    apply Subtype.ext
    change star (e (finiteOrthogonalColumn n (positiveSqrt M) (positiveSqrt N))) *
      e (finiteOrthogonalColumn n (positiveSqrt M) (positiveSqrt N)) =
      e (matrixInterleaveRaw n (M.1+N.1,0))
    rw [← map_star,← map_mul,finiteOrthogonalColumn_starMul,
      positiveSqrt_star M,positiveSqrt_star N,
      positiveSqrt_mul M,positiveSqrt_mul N]
  have hr : Positive.mulStar y = Positive.map (matrixInterleave n) (positiveProduct M N) := by
    apply Subtype.ext
    change e (finiteOrthogonalColumn n (positiveSqrt M) (positiveSqrt N)) *
      star (e (finiteOrthogonalColumn n (positiveSqrt M) (positiveSqrt N))) =
      e (matrixInterleaveRaw n (M.1,N.1))
    rw [← map_star,← map_mul,finiteOrthogonalColumn_mulStar n _ _
      (by simpa only [positiveSqrt_star N] using hcross)
      (by simpa only [positiveSqrt_star M] using hcross'),
      positiveSqrt_star M,positiveSqrt_star N,
      positiveSqrt_mul M,positiveSqrt_mul N]
  have h := finitePositiveClass_polar (n*2) y
  rw [hl,hr,finitePositiveClass_add,finitePositiveClass_add,
    finitePositiveClass_zero,add_zero] at h
  exact h

end Pureness
end

end OAI
