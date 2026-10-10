import OAI.Analysis.KadisonKastler.TracialCauchySchwarz
import OAI.Analysis.KadisonKastler.FiniteAveraging
import OAI.Analysis.FactorGeneration.MatrixUnits
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

namespace OAI

/-! # The normalized faithful trace on finite matrices

The normalized sum of the diagonal traces is positive and faithful by
expanding the diagonal entries of a matrix star square.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {B ι : Type*} [CStarAlgebra B] [Fintype ι]

local instance matrixTraceOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance matrixTraceStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

def matrixTraceLinearMap (τ : FaithfulTracialState B) :
    CStarMatrix ι ι B →ₗ[ℂ] ℂ where
  toFun x := (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) * ∑ i, τ.toLinearMap (x i i)
  map_add' x y := by
    simp [CStarMatrix.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    simp [CStarMatrix.smul_apply, Finset.mul_sum, mul_left_comm]

theorem matrixTraceLinearMap_apply (τ : FaithfulTracialState B)
    (x : CStarMatrix ι ι B) :
    matrixTraceLinearMap τ x =
      (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) * ∑ i, τ.toLinearMap (x i i) := rfl

theorem matrixTraceLinearMap_star_mul (τ : FaithfulTracialState B)
    (x : CStarMatrix ι ι B) :
    matrixTraceLinearMap τ (star x * x) =
      (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) *
        ∑ i, ∑ j, τ.toLinearMap (star (x j i) * x j i) := by
  simp only [matrixTraceLinearMap_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply, map_sum]

theorem matrixTraceLinearMap_star_mul_re (τ : FaithfulTracialState B)
    (x : CStarMatrix ι ι B) :
    (matrixTraceLinearMap τ (star x * x)).re =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∑ j, (τ.toLinearMap (star (x j i) * x j i)).re := by
  simp only [matrixTraceLinearMap_star_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]

theorem matrixTraceLinearMap_positive (τ : FaithfulTracialState B)
    (x : CStarMatrix ι ι B) : 0 ≤ (matrixTraceLinearMap τ (star x * x)).re := by
  rw [matrixTraceLinearMap_star_mul_re]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => τ.positive (x j i))

theorem matrixTraceLinearMap_positive_im (τ : FaithfulTracialState B)
    (x : CStarMatrix ι ι B) : (matrixTraceLinearMap τ (star x * x)).im = 0 := by
  simp only [matrixTraceLinearMap_star_mul, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.im_sum, τ.positive_im,
    Finset.sum_const_zero, mul_zero]

theorem matrixTraceLinearMap_tracial (τ : FaithfulTracialState B)
    (x y : CStarMatrix ι ι B) :
    matrixTraceLinearMap τ (x * y) = matrixTraceLinearMap τ (y * x) := by
  simp only [matrixTraceLinearMap_apply, CStarMatrix.mul_apply, map_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact τ.tracial _ _

variable [DecidableEq ι] [Nonempty ι]

theorem matrixTraceLinearMap_one (τ : FaithfulTracialState B) :
    matrixTraceLinearMap (ι := ι) τ 1 = 1 := by
  simp [matrixTraceLinearMap_apply, τ.map_one,
    Fintype.card_ne_zero]

omit [DecidableEq ι] in
theorem matrixTraceLinearMap_faithful (τ : FaithfulTracialState B)
    (x : CStarMatrix ι ι B) (hx : matrixTraceLinearMap τ (star x * x) = 0) : x = 0 := by
  have hsum : ∑ i, ∑ j, (τ.toLinearMap (star (x j i) * x j i)).re = 0 := by
    have hr := congrArg Complex.re hx
    rw [matrixTraceLinearMap_star_mul_re] at hr
    exact (mul_eq_zero.mp hr).resolve_left
      (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  have hcol (i : ι) : ∑ j, (τ.toLinearMap (star (x j i) * x j i)).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Finset.sum_nonneg fun j _ => τ.positive (x j k))).mp hsum i (Finset.mem_univ i)
  have hentry (i j : ι) : (τ.toLinearMap (star (x j i) * x j i)).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => τ.positive (x k i))).mp
      (hcol i) j (Finset.mem_univ j)
  ext i j
  exact τ.faithful (x i j) (Complex.ext (hentry j i) (τ.positive_im (x i j)))

/-- The canonical normalized faithful tracial state on finite square matrices. -/
def matrixTrace (τ : FaithfulTracialState B) : FaithfulTracialState (CStarMatrix ι ι B) where
  toLinearMap := matrixTraceLinearMap τ
  map_one := matrixTraceLinearMap_one τ
  positive := matrixTraceLinearMap_positive τ
  positive_im := matrixTraceLinearMap_positive_im τ
  faithful := matrixTraceLinearMap_faithful τ
  tracial := matrixTraceLinearMap_tracial τ

theorem matrixTrace_apply (τ : FaithfulTracialState B) (x : CStarMatrix ι ι B) :
    (matrixTrace τ).toLinearMap x =
      (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) * ∑ i, τ.toLinearMap (x i i) := rfl

/-- The canonical matrix units, with the identity of `B` in the selected entry. -/
def coordinateMatrixUnits : Generator.MatrixUnitSystem ι (CStarMatrix ι ι B) where
  entry i j := CStarMatrix.ofMatrix (Matrix.single i j (1 : B))
  star_entry i j := by
    change Matrix.conjTranspose (Matrix.single i j (1 : B)) = Matrix.single j i (1 : B)
    rw [Matrix.conjTranspose_single, star_one]
  mul_entry i j k l := by
    change Matrix.single i j (1 : B) * Matrix.single k l (1 : B) =
      if j = k then Matrix.single i l (1 : B) else 0
    by_cases h : j = k
    · subst k
      simp
    · rw [ite_eq_right h]
      exact Matrix.single_mul_single_of_ne (1 : B) i j k h 1
  total := by
    change (∑ i, Matrix.single i i (1 : B)) = 1
    exact Matrix.sum_single_one

omit [Nonempty ι] in
theorem coordinateMatrixUnits_projection (i : ι) :
    IsStarProjection ((coordinateMatrixUnits (B := B)).entry i i) :=
  (coordinateMatrixUnits (B := B)).diagonal_projection i

theorem matrixTrace_coordinate_diagonal (τ : FaithfulTracialState B) (i : ι) :
    (matrixTrace τ).toLinearMap ((coordinateMatrixUnits (B := B)).entry i i) =
      (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) := by
  simp [matrixTrace_apply, coordinateMatrixUnits, Matrix.single, apply_ite, τ.map_one]

omit [Nonempty ι] in
theorem finiteAverage_coordinate_diagonal :
    finiteAverage (fun i => (coordinateMatrixUnits (ι := ι) (B := B)).entry i i) =
      (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CStarMatrix ι ι B) := by
  rw [finiteAverage, (coordinateMatrixUnits (B := B)).total]
  simp

end

end KadisonKastler

end OAI
