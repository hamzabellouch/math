import OAI.Geometry.RCD.Coordinates.InverseDerivative
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-!
# Coercive Jacobians and changes of frozen metric

A lower metric estimate gives injectivity, hence an invertible Jacobian
in finite dimension. Taking the adjoint of `T ∘ e.symm` controls the
inverse transpose in the frozen dual norm, with no condition-number loss.
-/

noncomputable section

namespace RegularPointCoordinates

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The square-root form of the lower metric estimate. -/
theorem norm_le_sqrt_mul_of_metric_lower (T : E ≃L[ℝ] E) (J : E →L[ℝ] E)
    {A : ℝ} (hA : 1 ≤ A)
    (hlower : ∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖J xi‖ ^ 2) (xi : E) :
    ‖T xi‖ ≤ Real.sqrt A * ‖J xi‖ := by
  have hA0 : 0 < A := by linarith
  have hsquare : ‖T xi‖ ^ 2 ≤ A * ‖J xi‖ ^ 2 := by
    calc
      _ = A * (A⁻¹ * ‖T xi‖ ^ 2) := by field_simp [ne_of_gt hA0]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlower xi) hA0.le
  have hroot : (Real.sqrt A * ‖J xi‖) ^ 2 = A * ‖J xi‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA0.le]
  have hnonneg : 0 ≤ Real.sqrt A * ‖J xi‖ := by positivity
  nlinarith [norm_nonneg (T xi)]

/-- A coercive Jacobian has trivial kernel, in any normed dimension. -/
theorem injective_of_metric_lower (T : E ≃L[ℝ] E) (J : E →L[ℝ] E)
    {A : ℝ} (hA : 1 ≤ A)
    (hlower : ∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖J xi‖ ^ 2) :
    Function.Injective J := by
  intro x y hxy
  have hbound := norm_le_sqrt_mul_of_metric_lower T J hA hlower (x - y)
  have hnorm : ‖T (x - y)‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    simpa only [map_sub, hxy, sub_self, norm_zero, mul_zero] using hbound
  have hT := norm_eq_zero.mp hnorm
  have hzero : x - y = 0 := T.injective (by simpa using hT)
  exact sub_eq_zero.mp hzero

/-- In finite dimension the lower metric bound supplies the actual
continuous linear equivalence representing the Jacobian. -/
theorem exists_equiv_of_metric_lower [FiniteDimensional ℝ E]
    (T : E ≃L[ℝ] E) (J : E →L[ℝ] E) {A : ℝ} (hA : 1 ≤ A)
    (hlower : ∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖J xi‖ ^ 2) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = J := by
  let e := (LinearEquiv.ofInjectiveEndo J.toLinearMap
    (injective_of_metric_lower T J hA hlower)).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  ext x
  rfl

/-- The same construction supplies the unit premise used by the inverse
derivative lemmas. -/
theorem isUnit_of_metric_lower [FiniteDimensional ℝ E]
    (T : E ≃L[ℝ] E) (J : E →L[ℝ] E) {A : ℝ} (hA : 1 ≤ A)
    (hlower : ∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖J xi‖ ^ 2) : IsUnit J := by
  obtain ⟨e, he⟩ := exists_equiv_of_metric_lower T J hA hlower
  rw [← he]
  exact e.toUnit.isUnit

/-- The inverse Jacobian has norm at most `sqrt A` when its output is
measured using the frozen primal norm. -/
theorem norm_frozen_comp_inverse_le (T e : E ≃L[ℝ] E) {A : ℝ} (hA : 1 ≤ A)
    (hlower : ∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖e xi‖ ^ 2) :
    ‖(T : E →L[ℝ] E) ∘L (e.symm : E →L[ℝ] E)‖ ≤ Real.sqrt A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro y
  change ‖T (e.symm y)‖ ≤ Real.sqrt A * ‖y‖
  simpa using norm_le_sqrt_mul_of_metric_lower T (e : E →L[ℝ] E)
    hA hlower (e.symm y)

/-- Increasing frozen metrics make the next-to-current coordinate map
a contraction. -/
theorem norm_metric_change_le_one (Told Tnew : E ≃L[ℝ] E)
    (hmetric : ∀ xi, ‖Told xi‖ ≤ ‖Tnew xi‖) :
    ‖(Told : E →L[ℝ] E) ∘L (Tnew.symm : E →L[ℝ] E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  change ‖Told (Tnew.symm y)‖ ≤ 1 * ‖y‖
  simpa using hmetric (Tnew.symm y)

theorem norm_metric_change_le_one_of_sq (Told Tnew : E ≃L[ℝ] E)
    (hmetric : ∀ xi, ‖Told xi‖ ^ 2 ≤ ‖Tnew xi‖ ^ 2) :
    ‖(Told : E →L[ℝ] E) ∘L (Tnew.symm : E →L[ℝ] E)‖ ≤ 1 := by
  apply norm_metric_change_le_one Told Tnew
  intro xi
  nlinarith [hmetric xi, norm_nonneg (Told xi), norm_nonneg (Tnew xi)]

end Normed

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The inverse transpose factors through the frozen dual norm. -/
theorem inverseTranspose_frozen_factor (T e : E ≃L[ℝ] E) (w : E) :
    inverseTranspose e w =
      ((T : E →L[ℝ] E) ∘L (e.symm : E →L[ℝ] E)).adjoint
        ((T.symm : E →L[ℝ] E).adjoint w) := by
  have hcancel : (T.symm : E →L[ℝ] E) ∘L (T : E →L[ℝ] E) =
      ContinuousLinearMap.id ℝ E := by
    ext x
    simp
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    inverseTranspose]
  congr 1
  change w = ((T : E →L[ℝ] E).adjoint ∘L (T.symm : E →L[ℝ] E).adjoint) w
  rw [← ContinuousLinearMap.adjoint_comp, hcancel]
  rw [ContinuousLinearMap.adjoint_id]
  rfl

/-- Lower metric coercivity gives the dual inverse-transpose bound with
the same square-root constant. -/
theorem inverseTranspose_norm_le_frozen (T e : E ≃L[ℝ] E) {A : ℝ} (hA : 1 ≤ A)
    (hlower : ∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖e xi‖ ^ 2) (w : E) :
    ‖inverseTranspose e w‖ ≤ Real.sqrt A * ‖(T.symm : E →L[ℝ] E).adjoint w‖ := by
  let B : E →L[ℝ] E := (T : E →L[ℝ] E) ∘L (e.symm : E →L[ℝ] E)
  have hnorm : ‖B.adjoint‖ = ‖B‖ :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).norm_map B
  rw [inverseTranspose_frozen_factor T e w]
  calc
    _ ≤ ‖B.adjoint‖ * ‖(T.symm : E →L[ℝ] E).adjoint w‖ :=
      B.adjoint.le_opNorm _
    _ = ‖B‖ * ‖(T.symm : E →L[ℝ] E).adjoint w‖ := by rw [hnorm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (norm_frozen_comp_inverse_le T e hA hlower)
      (norm_nonneg _)

/-- Existence and the dual estimate may be obtained together directly
from the metric lower bound. -/
theorem exists_equiv_inverseTranspose_bound [FiniteDimensional ℝ E]
    (T : E ≃L[ℝ] E) (J : E →L[ℝ] E) {A : ℝ} (hA : 1 ≤ A)
    (hlower : ∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖J xi‖ ^ 2) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = J ∧
      ∀ w, ‖inverseTranspose e w‖ ≤ Real.sqrt A * ‖(T.symm : E →L[ℝ] E).adjoint w‖ := by
  obtain ⟨e, he⟩ := exists_equiv_of_metric_lower T J hA hlower
  refine ⟨e, he, ?_⟩
  apply inverseTranspose_norm_le_frozen T e hA
  simpa only [← he, ContinuousLinearEquiv.coe_coe] using hlower

end Hilbert

end RegularPointCoordinates

end

end OAI
