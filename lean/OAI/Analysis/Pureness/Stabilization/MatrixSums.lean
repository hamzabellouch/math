import Mathlib.Algebra.Order.Star.Pi
import OAI.Analysis.Pureness.Stabilization.ProductCuts
import OAI.Analysis.Pureness.Stabilization.MatrixTrace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi

namespace OAI
noncomputable section
open scoped NNReal ENNReal Topology CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def diagonalTwo : (Fin 2 → A) →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) A where
  toFun a := CStarMatrix.ofMatrix (Matrix.diagonal a)
  map_zero' := by ext i j; simp [Matrix.diagonal]
  map_add' a b := by ext i j; simp [Matrix.diagonal]; split_ifs <;> simp
  map_mul' a b := by
    change Matrix.diagonal (a*b) = Matrix.diagonal a * Matrix.diagonal b
    exact (Matrix.diagonal_mul_diagonal a b).symm
  map_smul' c a := by ext i j; simp [Matrix.diagonal, CStarMatrix.smul_apply]
  map_star' a := by ext i j; simp [Matrix.diagonal, CStarMatrix.star_apply]; split_ifs <;> simp_all

def coordinateTwo (i : Fin 2) : (Fin 2 → A) →⋆ₙₐ[ℂ] A where
  toFun a := a i
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma diagonalTwo_trace (τ : ExtendedTrace A) :
    (τ.matrixTrace (Fin 2)).pullback diagonalTwo =
      τ.pullback (coordinateTwo 0) + τ.pullback (coordinateTwo 1) := by
  ext p
  change (τ.matrixTrace (Fin 2)) (Positive.map diagonalTwo p) =
    τ (Positive.map (coordinateTwo 0) p) + τ (Positive.map (coordinateTwo 1) p)
  rw [ExtendedTrace.matrixTrace_apply, Fin.sum_univ_two]
  congr 1

def positivePair (a b : Positive A) : Positive (Fin 2 → A) :=
  ⟨![a.1,b.1], by intro i; fin_cases i <;> simp [a.2,b.2]⟩

def blockSum (a b : Positive A) : Positive (CStarMatrix (Fin 2) (Fin 2) A) :=
  Positive.map diagonalTwo (positivePair a b)

lemma blockSum_rank (τ : ExtendedTrace A) (a b : Positive A) :
    (τ.matrixTrace (Fin 2)).rank (blockSum a b) = τ.rank a + τ.rank b := by
  rw [blockSum, ← ExtendedTrace.rank_pullback, diagonalTwo_trace, ExtendedTrace.rank_add,
    ExtendedTrace.rank_pullback, ExtendedTrace.rank_pullback]
  rfl

lemma sum_corner_cuntzBelow_blockSum (a b : Positive A) :
    CuntzBelow (Positive.map (matrixCorner (0 : Fin 2)) (Positive.add a b)) (blockSum a b) := by
  let s := CFC.sqrt a.1
  let t := CFC.sqrt b.1
  have hs : star s = s := (CFC.sqrt_nonneg a.1).star_eq
  have ht : star t = t := (CFC.sqrt_nonneg b.1).star_eq
  have hs2 : s*s = a.1 := CFC.sqrt_mul_sqrt_self a.1 a.2
  have ht2 : t*t = b.1 := CFC.sqrt_mul_sqrt_self b.1 b.2
  let R : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![s,t;0,0]
  let N : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![s,-t;0,0]
  have hR : Positive.mulStar R = Positive.map (matrixCorner (0 : Fin 2)) (Positive.add a b) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, Positive.mulStar, Positive.map, Positive.add, matrixCorner, Matrix.single,
        CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two, hs, ht, hs2, ht2]
  have hsum : star R*R + star N*N = (2 : ℝ) • (blockSum a b).1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, N, blockSum, positivePair, Positive.map, diagonalTwo, Matrix.diagonal,
        CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.smul_apply, Fin.sum_univ_two,
        hs, ht, hs2, ht2, two_smul]
  have hle : (Positive.starMul R).1 ≤ (2 : ℝ) • (blockSum a b).1 := by
    rw [← hsum]
    exact le_add_of_nonneg_right (star_mul_self_nonneg N)
  rw [← hR]
  exact (mulStar_cuntzBelow_starMul R).trans (CuntzBelow.of_le_smul _ _ 2 (by norm_num) hle)

lemma rank_positive_add_le (τ : ExtendedTrace A) (a b : Positive A) :
    τ.rank (Positive.add a b) ≤ τ.rank a + τ.rank b := by
  rw [← τ.matrixRank_corner (0 : Fin 2), ← blockSum_rank]
  exact (τ.matrixTrace (Fin 2)).rank_le_of_cuntzBelow (sum_corner_cuntzBelow_blockSum a b)

lemma rank_abs_add_le (τ : ExtendedTrace A) (x y : A) :
    τ.rank (Positive.abs (x+y)) ≤ τ.rank (Positive.abs x) + τ.rank (Positive.abs y) := by
  have ho : (Positive.starMul (x+y)).1 ≤ (2 : ℝ) • (Positive.add (Positive.starMul x) (Positive.starMul y)).1 := by
    have h := starMul_add_le x y 1 zero_lt_one
    norm_num at h
    simpa only [Positive.starMul, Positive.add, smul_add, star_add] using h
  have h := τ.rank_le_of_cuntzBelow ((abs_cuntzBelow_starMul (x+y)).trans
    (CuntzBelow.of_le_smul _ _ 2 (by norm_num) ho))
  exact h.trans ((rank_positive_add_le τ _ _).trans (add_le_add
    (τ.rank_le_of_cuntzBelow (starMul_cuntzBelow_abs x))
    (τ.rank_le_of_cuntzBelow (starMul_cuntzBelow_abs y))))

theorem sum_cut_rank (τ : ExtendedTrace A) (x y : A) (ε : ℝ≥0) (hε : 0 < ε) :
    τ.rank (Positive.cut ε (Positive.abs (x+y))) ≤
      τ.rank (Positive.cut (ε/4) (Positive.abs x)) + τ.rank (Positive.cut (ε/4) (Positive.abs y)) := by
  obtain ⟨u, hu, hau⟩ := exists_cut_truncation x (ε/4) (by positivity)
  obtain ⟨v, hv, hav⟩ := exists_cut_truncation y (ε/4) (by positivity)
  have hn : ‖(x+y)-(u+v)‖ < ε := by
    have he : (x+y)-(u+v) = (x-u)+(y-v) := by abel
    rw [he]
    have hu' : ‖x-u‖ ≤ (ε : ℝ)/4 := by exact_mod_cast hu
    have hv' : ‖y-v‖ ≤ (ε : ℝ)/4 := by exact_mod_cast hv
    exact (norm_add_le _ _).trans_lt (by linarith [show (0 : ℝ) < ε from hε])
  have h := τ.rank_le_of_cuntzBelow (abs_cut_cuntzBelow_of_norm_sub_lt (x+y) (u+v) ε hε hn)
  exact h.trans (by simpa only [hau, hav] using rank_abs_add_le τ u v)
end CuntzTrace

end

end OAI
