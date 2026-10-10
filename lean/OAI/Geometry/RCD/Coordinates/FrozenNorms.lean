import OAI.Geometry.RCD.Coordinates.PositiveForms

namespace OAI

/-!
# Frozen primal and dual norms

A continuous linear equivalence `T` represents the frozen square root
of the source metric.  The primal norm is `‖T x‖`, and the dual norm is
`‖(T.symm).adjoint w‖`.  Congruence by the inverse of `T` transports the
positive-form bounds to Euclidean norms without a condition-number loss.
No construction or differentiation of a matrix square root is required.
-/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A covariant positive form in frozen Euclidean coordinates. -/
def frozenConjugate (T : E ≃L[ℝ] E) (D : E →L[ℝ] E) : E →L[ℝ] E :=
  (T.symm : E →L[ℝ] E).adjoint ∘L D ∘L (T.symm : E →L[ℝ] E)

theorem inner_frozenConjugate (T : E ≃L[ℝ] E) (D : E →L[ℝ] E) (x y : E) :
    ⟪x, frozenConjugate T D y⟫_ℝ = ⟪T.symm x, D (T.symm y)⟫_ℝ := by
  simp only [frozenConjugate, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem frozenConjugate_apply_primal (T : E ≃L[ℝ] E) (D : E →L[ℝ] E) (w : E) :
    frozenConjugate T D (T w) = (T.symm : E →L[ℝ] E).adjoint (D w) := by
  simp [frozenConjugate]

/-- Congruence preserves positivity even when the mass form is singular. -/
theorem frozenConjugate_isPositive (T : E ≃L[ℝ] E) {D : E →L[ℝ] E}
    (hD : D.IsPositive) : (frozenConjugate T D).IsPositive :=
  hD.adjoint_conj (T.symm : E →L[ℝ] E)

/-- A bound by the frozen source metric becomes a Euclidean form bound. -/
theorem frozenConjugate_form_bound (T : E ≃L[ℝ] E) {D : E →L[ℝ] E}
    {epsilon : ℝ} (hbound : ∀ x, ⟪x, D x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2) (z : E) :
    ⟪z, frozenConjugate T D z⟫_ℝ ≤ epsilon * ‖z‖ ^ 2 := by
  rw [inner_frozenConjugate]
  simpa using hbound (T.symm z)

/-- The sharp anisotropic positive-matrix estimate: the dual norm of
`D w` is controlled by its own directional mass, not by the full metric. -/
theorem frozen_positive_form_norm_sq_le (T : E ≃L[ℝ] E) {D : E →L[ℝ] E}
    (hD : D.IsPositive) {epsilon : ℝ}
    (hbound : ∀ x, ⟪x, D x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2) (w : E) :
    ‖(T.symm : E →L[ℝ] E).adjoint (D w)‖ ^ 2 ≤ epsilon * ⟪w, D w⟫_ℝ := by
  have h := positive_form_norm_sq_le (frozenConjugate_isPositive T hD)
    (frozenConjugate_form_bound T hbound) (T w)
  rw [inner_frozenConjugate] at h
  simpa only [frozenConjugate_apply_primal, ContinuousLinearEquiv.symm_apply_apply] using h

/-- The same estimate in square-root form. -/
theorem frozen_positive_form_norm_le (T : E ≃L[ℝ] E) {D : E →L[ℝ] E}
    (hD : D.IsPositive) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ x, ⟪x, D x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2) (w : E) :
    ‖(T.symm : E →L[ℝ] E).adjoint (D w)‖ ≤
      Real.sqrt epsilon * Real.sqrt ⟪w, D w⟫_ℝ := by
  have h := positive_form_norm_le (frozenConjugate_isPositive T hD) hepsilon
    (frozenConjugate_form_bound T hbound) (T w)
  rw [inner_frozenConjugate] at h
  simpa only [frozenConjugate_apply_primal, ContinuousLinearEquiv.symm_apply_apply] using h

/-- Primal-dual pairing is invariant under the frozen normalization. -/
theorem inner_primal_dual (T : E ≃L[ℝ] E) (x w : E) :
    ⟪T x, (T.symm : E →L[ℝ] E).adjoint w⟫_ℝ = ⟪x, w⟫_ℝ := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp

theorem abs_inner_le_frozen_primal_mul_dual (T : E ≃L[ℝ] E) (x w : E) :
    |⟪x, w⟫_ℝ| ≤ ‖T x‖ * ‖(T.symm : E →L[ℝ] E).adjoint w‖ := by
  rw [← inner_primal_dual T x w]
  exact abs_real_inner_le_norm _ _

/-- Positive-form Cauchy--Schwarz has unchanged directional energies
after the frozen normalization. -/
theorem frozen_positive_form_inner_abs_le (T : E ≃L[ℝ] E) {D : E →L[ℝ] E}
    (hD : D.IsPositive) (x y : E) :
    |⟪T x, frozenConjugate T D (T y)⟫_ℝ| ≤
      Real.sqrt ⟪x, D x⟫_ℝ * Real.sqrt ⟪y, D y⟫_ℝ := by
  rw [inner_frozenConjugate]
  simpa using positive_form_inner_abs_le hD x y

/-- The same small form has mixed operator norm at most `epsilon`,
from the frozen primal norm to its dual norm. -/
theorem frozen_positive_form_norm_le_primal (T : E ≃L[ℝ] E) {D : E →L[ℝ] E}
    (hD : D.IsPositive) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ x, ⟪x, D x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2) (w : E) :
    ‖(T.symm : E →L[ℝ] E).adjoint (D w)‖ ≤ epsilon * ‖T w‖ := by
  have hsq := frozen_positive_form_norm_sq_le T hD hbound w
  have hsmall := mul_le_mul_of_nonneg_left (hbound w) hepsilon
  have htarget : 0 ≤ epsilon * ‖T w‖ := mul_nonneg hepsilon (norm_nonneg _)
  nlinarith [norm_nonneg ((T.symm : E →L[ℝ] E).adjoint (D w))]

theorem frozen_positive_form_mixed_opNorm_le (T : E ≃L[ℝ] E) {D : E →L[ℝ] E}
    (hD : D.IsPositive) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ x, ⟪x, D x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2) :
    ‖frozenConjugate T D‖ ≤ epsilon := by
  apply ContinuousLinearMap.opNorm_le_bound _ hepsilon
  intro z
  have h := frozen_positive_form_norm_le_primal T hD hepsilon hbound (T.symm z)
  simpa [frozenConjugate] using h

/-- A directional displacement-energy estimate gives the dual field-value
bound used by each patch. -/
theorem frozen_positive_form_value_le (T : E ≃L[ℝ] E) {D : E →L[ℝ] E}
    (hD : D.IsPositive) {epsilon C r energy : ℝ}
    (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C) (hr : 0 ≤ r) (henergy : 0 ≤ energy)
    (hbound : ∀ x, ⟪x, D x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2)
    (w : E) (hw : ⟪w, D w⟫_ℝ ≤ C * r ^ 2 * energy) :
    ‖(T.symm : E →L[ℝ] E).adjoint (D w)‖ ≤
      Real.sqrt epsilon * Real.sqrt C * r * Real.sqrt energy := by
  have hsq := (frozen_positive_form_norm_sq_le T hD hbound w).trans
    (mul_le_mul_of_nonneg_left hw hepsilon)
  have hroot : (Real.sqrt epsilon * Real.sqrt C * r * Real.sqrt energy) ^ 2 =
      epsilon * C * r ^ 2 * energy := by
    simp only [mul_pow, Real.sq_sqrt hepsilon, Real.sq_sqrt hC, Real.sq_sqrt henergy]
  have hnonneg : 0 ≤ Real.sqrt epsilon * Real.sqrt C * r * Real.sqrt energy := by positivity
  nlinarith [norm_nonneg ((T.symm : E →L[ℝ] E).adjoint (D w))]

/-- Finite cutoff errors and field values may be estimated in the same
dual norm while retaining each patch's directional energy. -/
theorem frozen_positive_patch_sum_norm_le {ι : Type*}
    (T : E ≃L[ℝ] E) (s : Finset ι) (D : ι → E →L[ℝ] E)
    (w : ι → E) (a : ι → ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hD : ∀ j ∈ s, (D j).IsPositive)
    (hbound : ∀ j ∈ s, ∀ x, ⟪x, D j x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2) :
    ‖(T.symm : E →L[ℝ] E).adjoint (∑ j ∈ s, a j • D j (w j))‖ ≤
      ∑ j ∈ s, |a j| * (Real.sqrt epsilon * Real.sqrt ⟪w j, D j (w j)⟫_ℝ) := by
  rw [map_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [map_smul, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (frozen_positive_form_norm_le T (hD j hj) hepsilon (hbound j hj) (w j)) (abs_nonneg _)

end RegularPointCoordinates

end

end OAI
