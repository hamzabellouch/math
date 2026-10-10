import Mathlib
import OAI.Geometry.CAT0Fillings.Geometry.Determinant

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped RealInnerProductSpace MatrixOrder

noncomputable def matrixRowFunctional {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := ∑ j, M i j • EuclideanSpace.proj j

@[simp] lemma matrixRowFunctional_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    matrixRowFunctional M i v = M i ⬝ᵥ v := by
  simp [matrixRowFunctional,dotProduct]

@[simp] lemma matrixRowFunctional_single {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : matrixRowFunctional M i (EuclideanSpace.single j 1) = M i j := by
  simp [dotProduct]

lemma norm_sqrt_mulVec {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (v : Fin n → ℝ) :
    ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (v ⬝ᵥ P.mulVec v) := by
  rw [dot_mulVec_sqrt P hP]
  have heq : (CFC.sqrt P).mulVec v ⬝ᵥ (CFC.sqrt P).mulVec v =
      ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,star_trivial] using
      real_inner_self_eq_norm_sq
        (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))
  rw [heq,Real.sqrt_sq (norm_nonneg _)]

lemma sqrt_det_le_mul_sqrt_det {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (hQ : Q.PosDef) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Fin n → ℝ,
      Real.sqrt (v ⬝ᵥ P.mulVec v) ≤ K*Real.sqrt (v ⬝ᵥ Q.mulVec v)) :
    Real.sqrt P.det ≤ K^n * Real.sqrt Q.det := by
  let A := CFC.sqrt P
  let B := CFC.sqrt Q
  have hAdet : A.det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.det_sqrt
  have hBdet : B.det = Real.sqrt Q.det := by
    simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt
  have hBp : 0 < B.det := by rw [hBdet]; exact Real.sqrt_pos.2 hQ.det_pos
  have hBi : IsUnit B.det := isUnit_iff_ne_zero.2 (ne_of_gt hBp)
  have hBinv := Matrix.mul_nonsing_inv B hBi
  have hinvB := Matrix.nonsing_inv_mul B hBi
  have htrans (v : Fin n → ℝ) :
      Real.sqrt ((B⁻¹).mulVec v ⬝ᵥ Q.mulVec ((B⁻¹).mulVec v)) =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    rw [←norm_sqrt_mulVec Q hQ.posSemidef]
    change ‖(WithLp.toLp 2 (B.mulVec ((B⁻¹).mulVec v)) : EuclideanSpace ℝ (Fin n))‖ = _
    rw [Matrix.mulVec_mulVec,hBinv,Matrix.one_mulVec]
  have hbound : |(A * B⁻¹).det| ≤ K^n := by
    apply abs_det_le_pow_of_dot_bound _ hK
    intro i v
    have hh := h ((B⁻¹).mulVec v)
    rw [htrans,←norm_sqrt_mulVec P hP] at hh
    apply le_trans _ hh
    have hv : (A * B⁻¹) i ⬝ᵥ v = (A.mulVec ((B⁻¹).mulVec v)) i := by
      rw [Matrix.mulVec_mulVec]
      rfl
    rw [hv]
    exact PiLp.norm_apply_le
      (WithLp.toLp 2 (A.mulVec ((B⁻¹).mulVec v)) : EuclideanSpace ℝ (Fin n)) i
  have heq : A = (A*B⁻¹)*B := by rw [Matrix.mul_assoc,hinvB,Matrix.mul_one]
  calc
    Real.sqrt P.det = |A.det| := by rw [hAdet,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ = |(A*B⁻¹).det| *B.det := by
      conv_lhs => rw [heq,Matrix.det_mul]
      rw [abs_mul,abs_of_pos hBp]
    _ ≤ K^n*B.det := mul_le_mul_of_nonneg_right hbound hBp.le
    _ = K^n*Real.sqrt Q.det := by rw [hBdet]

lemma abs_matrixRow_sqrt_le {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (i : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    |matrixRowFunctional (CFC.sqrt P) i v| ≤ Real.sqrt (v ⬝ᵥ P.mulVec v) := by
  rw [matrixRowFunctional_apply,←norm_sqrt_mulVec P hP]
  exact PiLp.norm_apply_le
    (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n)) i

end CAT0Fillings

end

end OAI
