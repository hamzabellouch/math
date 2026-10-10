import Mathlib

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
lemma abs_det_le_prod_row_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have h := b.toBasis.orientation.abs_volumeForm_apply_le
    (fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n)))
  rw [Orientation.volumeForm_robust _ b rfl, Module.Basis.det_apply] at h
  convert h using 1
  congr 1
  have heq : b.toBasis.toMatrix (fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))) = A.transpose := by
    ext i j
    simp [b, Module.Basis.toMatrix_apply]
  rw [heq, Matrix.det_transpose]

lemma row_norm_le_of_dot_bound {n : ℕ} (a : Fin n → ℝ)
    (h : ∀ v : Fin n → ℝ, |a ⬝ᵥ v| ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
  have hh := h a
  have heq : a ⬝ᵥ a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
      real_inner_self_eq_norm_sq (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))
  rw [heq,abs_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))]

lemma abs_det_le_one_of_dot_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i v, |A i ⬝ᵥ v| ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    |A.det| ≤ 1 := by
  apply (abs_det_le_prod_row_norm A).trans
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => row_norm_le_of_dot_bound _ (h i))

lemma dot_mulVec_sqrt {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (v : Fin n → ℝ) :
    v ⬝ᵥ P.mulVec v = (CFC.sqrt P).mulVec v ⬝ᵥ (CFC.sqrt P).mulVec v := by
  have hsym : (CFC.sqrt P).transpose = CFC.sqrt P :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P).posSemidef.isHermitian).eq
  conv_lhs => rw [← CFC.sq_sqrt P hP.nonneg,pow_two, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]

lemma abs_det_le_sqrt_det_of_posDef {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef)
    (h : ∀ i v, |L i ⬝ᵥ v| ≤ Real.sqrt (v ⬝ᵥ P.mulVec v)) :
    |L.det| ≤ Real.sqrt P.det := by
  let Q := CFC.sqrt P
  have hQdet : Q.det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.posSemidef.det_sqrt
  have hQpos : 0 < Q.det := by rw [hQdet]; exact Real.sqrt_pos.2 hP.det_pos
  have hQi : IsUnit Q.det := isUnit_iff_ne_zero.2 (ne_of_gt hQpos)
  have hQinv := Matrix.mul_nonsing_inv Q hQi
  have hinvQ := Matrix.nonsing_inv_mul Q hQi
  have htrans (v : Fin n → ℝ) :
      Real.sqrt ((Q⁻¹).mulVec v ⬝ᵥ P.mulVec ((Q⁻¹).mulVec v)) =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    rw [dot_mulVec_sqrt P hP.posSemidef]
    change Real.sqrt (Q.mulVec ((Q⁻¹).mulVec v) ⬝ᵥ Q.mulVec ((Q⁻¹).mulVec v)) = _
    rw [Matrix.mulVec_mulVec, hQinv, Matrix.one_mulVec]
    have hn : v ⬝ᵥ v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
        real_inner_self_eq_norm_sq (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
    rw [hn,Real.sqrt_sq (norm_nonneg _)]
  have hB : |(L * Q⁻¹).det| ≤ 1 := by
    apply abs_det_le_one_of_dot_bound
    intro i v
    have hh := h i ((Q⁻¹).mulVec v)
    rw [htrans] at hh
    convert hh using 1
    congr 1
    change ((L * Q⁻¹).mulVec v) i = (L.mulVec ((Q⁻¹).mulVec v)) i
    rw [Matrix.mulVec_mulVec]
  have heq : L = (L * Q⁻¹) * Q := by rw [Matrix.mul_assoc,hinvQ,Matrix.mul_one]
  calc
    |L.det| = |(L * Q⁻¹).det| * Q.det := by
      conv_lhs => rw [heq, Matrix.det_mul]
      rw [abs_mul,abs_of_pos hQpos]
    _ ≤ 1*Q.det := mul_le_mul_of_nonneg_right hB hQpos.le
    _ = Real.sqrt P.det := by rw [one_mul,hQdet]

theorem abs_det_le_sqrt_det_of_posSemidef {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef)
    (h : ∀ i v, |L i ⬝ᵥ v| ≤ Real.sqrt (v ⬝ᵥ P.mulVec v)) :
    |L.det| ≤ Real.sqrt P.det := by
  by_cases hzero : P.det = 0
  · obtain ⟨v,hv,hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hzero
    have hLv : L.mulVec v = 0 := by
      ext i
      have hh := h i v
      rw [hPv, dotProduct_zero,Real.sqrt_zero] at hh
      exact abs_nonpos_iff.mp hh
    have hL := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v,hv,hLv⟩
    rw [hL,hzero,abs_zero,Real.sqrt_zero]
  · apply abs_det_le_sqrt_det_of_posDef L P _ h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hP.isHermitian
    intro v hv
    refine lt_of_le_of_ne (hP.dotProduct_mulVec_nonneg v) ?_
    intro heq
    have hz := hP.dotProduct_mulVec_zero_iff.1 heq.symm
    exact hv (Matrix.eq_zero_of_mulVec_eq_zero hzero hz)
lemma row_norm_le_of_dot_bound_const {n : ℕ} (a : Fin n → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Fin n → ℝ, |a ⬝ᵥ v| ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ ≤ K := by
  have hh := h a
  have heq : a ⬝ᵥ a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
      real_inner_self_eq_norm_sq (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))
  rw [heq,abs_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))]

lemma abs_det_le_pow_of_dot_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i v, |A i ⬝ᵥ v| ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    |A.det| ≤ K^n := by
  apply (abs_det_le_prod_row_norm A).trans
  calc
    _ ≤ ∏ _i : Fin n, K := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => row_norm_le_of_dot_bound_const _ hK (h i))
    _ = K^n := by simp

lemma sqrt_det_le_pow_of_quadratic_bound {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Fin n → ℝ,
      Real.sqrt (v ⬝ᵥ P.mulVec v) ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    Real.sqrt P.det ≤ K^n := by
  have hdet : (CFC.sqrt P).det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.det_sqrt
  rw [←hdet]
  have hdnonneg : 0 ≤ (CFC.sqrt P).det := by rw [hdet]; exact Real.sqrt_nonneg _
  rw [←abs_of_nonneg hdnonneg]
  apply abs_det_le_pow_of_dot_bound _ hK
  intro i v
  have hn : ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (v ⬝ᵥ P.mulVec v) := by
    rw [dot_mulVec_sqrt P hP]
    have heq : (CFC.sqrt P).mulVec v ⬝ᵥ (CFC.sqrt P).mulVec v =
        ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
        real_inner_self_eq_norm_sq
          (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))
    rw [heq, Real.sqrt_sq (norm_nonneg _)]
  apply le_trans _ (h v)
  rw [←hn]
  exact PiLp.norm_apply_le (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n)) i

end CAT0Fillings

end

end OAI
