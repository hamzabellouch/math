import OAI.Geometry.RCD.Coordinates.LinearNormalization
import OAI.Geometry.RCD.Coordinates.WeightedInverse

namespace OAI

/-! # Exact Euclidean frames for the inverse heat metrics -/

open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- An invertible positive form is strictly positive on nonzero vectors. -/
theorem positive_equiv_strict (Q : E ≃L[ℝ] E)
    (hQ : Q.toContinuousLinearMap.IsPositive) {v : E} (hv : v ≠ 0) :
    0 < ⟪v, Q v⟫_ℝ := by
  have hn := hQ.inner_nonneg_right v
  apply lt_of_le_of_ne hn
  intro hz
  have h := positive_form_cauchy_schwarz hQ (Q v) v
  simp only [ContinuousLinearEquiv.coe_coe] at h hz
  rw [← hz, mul_zero, real_inner_self_eq_norm_sq] at h
  have hs : ‖Q v‖ ^ 2 = 0 := by nlinarith [sq_nonneg (‖Q v‖ ^ 2)]
  have hzero : Q v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
  exact hv (Q.injective (by simpa only [map_zero] using hzero))

/-- A finite-dimensional inverse metric represented by an actual linear frame. -/
def inverseMetricFrame (Q : E ≃L[ℝ] E)
    (hQ : Q.toContinuousLinearMap.IsPositive) : E ≃L[ℝ] E :=
  (Classical.choose (exists_exact_operator_normalization Q.symm.toContinuousLinearMap
    (positive_equiv_symm Q hQ).isSymmetric
    (fun _ hv => positive_equiv_strict Q.symm (positive_equiv_symm Q hQ) hv))).symm

@[simp] theorem inverseMetricFrame_norm_sq (Q : E ≃L[ℝ] E)
    (hQ : Q.toContinuousLinearMap.IsPositive) (v : E) :
    ‖inverseMetricFrame Q hQ v‖ ^ 2 = ⟪v, Q.symm v⟫_ℝ := by
  let A := (inverseMetricFrame Q hQ).symm
  have he : A.toContinuousLinearMap.adjoint.comp
      (Q.symm.toContinuousLinearMap.comp A.toContinuousLinearMap) =
        ContinuousLinearMap.id ℝ E :=
    Classical.choose_spec (exists_exact_operator_normalization Q.symm.toContinuousLinearMap
      (positive_equiv_symm Q hQ).isSymmetric
      (fun _ hv => positive_equiv_strict Q.symm (positive_equiv_symm Q hQ) hv))
  have h := congrArg (fun T : E →L[ℝ] E => ⟪A.symm v, T (A.symm v)⟫_ℝ) he
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] at h
  exact h.symm

/-- Decreasing positive forms have increasing inverse-frame norms. -/
theorem inverseMetricFrame_mono (P Q : E ≃L[ℝ] E)
    (hP : P.toContinuousLinearMap.IsPositive) (hQ : Q.toContinuousLinearMap.IsPositive)
    (hD : (P.toContinuousLinearMap - Q.toContinuousLinearMap).IsPositive) (v : E) :
    ‖inverseMetricFrame P hP v‖ ≤ ‖inverseMetricFrame Q hQ v‖ := by
  have h := (inverse_increment_isPositive P Q hP hQ hD).inner_nonneg_right v
  simp only [sub_apply, inner_sub_right, ContinuousLinearEquiv.coe_coe] at h
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [inverseMetricFrame_norm_sq]
  linarith only [h]

/-- Slow heat decay gives a uniform comparison of successive frozen frames. -/
theorem inverseMetricFrame_step (P Q : E ≃L[ℝ] E)
    (hP : P.toContinuousLinearMap.IsPositive) (hQ : Q.toContinuousLinearMap.IsPositive)
    (hstep : ∀ v, ⟪v, P v⟫_ℝ ≤ (9 / 8 : ℝ) * ⟪v, Q v⟫_ℝ) (v : E) :
    ‖inverseMetricFrame Q hQ v‖ ≤ 2 * ‖inverseMetricFrame P hP v‖ := by
  have hc (w : E) : (8 / 9 : ℝ) * ⟪w, P w⟫_ℝ ≤ ⟪w, Q w⟫_ℝ := by
    have h := hstep w
    linarith
  have h := (relative_inverse_bounds P Q hP hQ (by norm_num : (0 : ℝ) < 8 / 9) hc v).1
  rw [← inverseMetricFrame_norm_sq Q hQ, ← inverseMetricFrame_norm_sq P hP] at h
  nlinarith [sq_nonneg (‖inverseMetricFrame P hP v‖), norm_nonneg (inverseMetricFrame Q hQ v),
    norm_nonneg (inverseMetricFrame P hP v)]

omit [FiniteDimensional ℝ E] in
/-- A relative half-small decrement controls the inverse discrepancy in
both endpoint metrics, including the finer metric used by patch assembly. -/
theorem inverse_difference_energy_le (P Q : E ≃L[ℝ] E)
    (hP : P.toContinuousLinearMap.IsPositive) (hQ : Q.toContinuousLinearMap.IsPositive)
    (hD : (P.toContinuousLinearMap - Q.toContinuousLinearMap).IsPositive)
    (hstep : ∀ v, ⟪v, P v⟫_ℝ ≤ 2 * ⟪v, Q v⟫_ℝ) (xi : E) :
    let d := Q.symm xi - P.symm xi
    ⟪d, Q d⟫_ℝ ≤ ⟪xi, Q.symm xi⟫_ℝ - ⟪xi, P.symm xi⟫_ℝ := by
  intro d
  have hsmall (v : E) : ⟪v, (P.toContinuousLinearMap - Q.toContinuousLinearMap) v⟫_ℝ ≤
      (1 / 2 : ℝ) * ⟪v, P v⟫_ℝ := by
    simp only [sub_apply, inner_sub_right, ContinuousLinearEquiv.coe_coe]
    linarith only [hstep v]
  have h := inverse_increment_weighted_square_le P Q hP hQ hD hsmall xi
  have hm := hD.inner_nonneg_right d
  simp only [sub_apply, inner_sub_right, ContinuousLinearEquiv.coe_coe] at h hm
  change ⟪d, P d⟫_ℝ ≤ ⟪xi, Q.symm xi⟫_ℝ - ⟪xi, P.symm xi⟫_ℝ at h
  linarith only [h, hm]

end RegularPointCoordinates

end

end OAI
