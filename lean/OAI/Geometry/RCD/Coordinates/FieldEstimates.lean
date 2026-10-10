import OAI.Geometry.RCD.Coordinates.PositiveForms
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace OAI

/-!
# First derivatives of the value-space patch field

The local mass operators may be singular. Their positivity controls the
error from differentiating the cutoffs by the directional mass, rather than
by the full norm of the local metric.
-/

open scoped BigOperators InnerProductSpace

namespace RegularPointCoordinates

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The field used by the renormalization, written as a finite patch sum. -/
def patchField (s : Finset ι) (phi : ι → E → ℝ) (D : ι → E →L[ℝ] E)
    (c : ι → E) (P : E) : E :=
  ∑ j ∈ s, phi j P • D j (P - c j)

/-- Its derivative consists of the principal positive mass plus cutoff errors. -/
theorem hasFDerivAt_patchField (s : Finset ι) (phi : ι → E → ℝ)
    (dphi : ι → E →L[ℝ] ℝ) (D : ι → E →L[ℝ] E) (c : ι → E) (P : E)
    (hphi : ∀ j ∈ s, HasFDerivAt (phi j) (dphi j) P) :
    HasFDerivAt (patchField s phi D c)
      (∑ j ∈ s, ((phi j P) • D j + (dphi j).smulRight (D j (P - c j)))) P := by
  have hterm : ∀ j ∈ s, HasFDerivAt (fun y => phi j y • D j (y - c j))
      ((phi j P) • D j + (dphi j).smulRight (D j (P - c j))) P := by
    intro j hj
    have hD := (D j).hasFDerivAt.comp P ((hasFDerivAt_id P).sub_const (c j))
    simpa [Function.comp_def] using (hphi j hj).fun_smul hD
  convert HasFDerivAt.sum hterm using 1
  ext y
  simp [patchField]

/-- A finite cutoff error is bounded by the square root of the directional
mass times the square root of the displacement energy. -/
theorem patch_error_inner_le (s : Finset ι) (D : ι → E →L[ℝ] E)
    (w : ι → E) (a : ι → ℝ) (xi : E) {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ j ∈ s, (D j).IsPositive) (ha : ∀ j ∈ s, |a j| ≤ K) :
    |⟪xi, ∑ j ∈ s, a j • D j (w j)⟫_ℝ| ≤
      K * Real.sqrt (∑ j ∈ s, ⟪xi, D j xi⟫_ℝ) *
        Real.sqrt (∑ j ∈ s, ⟪w j, D j (w j)⟫_ℝ) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun j => Real.sqrt ⟪xi, D j xi⟫_ℝ)
    (fun j => Real.sqrt ⟪w j, D j (w j)⟫_ℝ)
  have hx : (∑ j ∈ s, (Real.sqrt ⟪xi, D j xi⟫_ℝ) ^ 2) =
      ∑ j ∈ s, ⟪xi, D j xi⟫_ℝ :=
    Finset.sum_congr rfl (fun j hj => Real.sq_sqrt ((hD j hj).inner_nonneg_right xi))
  have hw : (∑ j ∈ s, (Real.sqrt ⟪w j, D j (w j)⟫_ℝ) ^ 2) =
      ∑ j ∈ s, ⟪w j, D j (w j)⟫_ℝ :=
    Finset.sum_congr rfl (fun j hj => Real.sq_sqrt ((hD j hj).inner_nonneg_right (w j)))
  rw [hx, hw] at hcs
  calc
    _ = |∑ j ∈ s, a j * ⟪xi, D j (w j)⟫_ℝ| := by
      simp only [inner_sum, inner_smul_right]
    _ ≤ ∑ j ∈ s, |a j * ⟪xi, D j (w j)⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, K *
        (Real.sqrt ⟪xi, D j xi⟫_ℝ * Real.sqrt ⟪w j, D j (w j)⟫_ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (ha j hj) (positive_form_inner_abs_le (hD j hj) xi (w j))
        (abs_nonneg _) hK
    _ = K * ∑ j ∈ s,
        Real.sqrt ⟪xi, D j xi⟫_ℝ * Real.sqrt ⟪w j, D j (w j)⟫_ℝ := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs hK

/-- The principal part of the derivative is positive when the cutoffs are. -/
theorem patch_principal_isPositive (s : Finset ι) (phi : ι → ℝ)
    (D : ι → E →L[ℝ] E)
    (hphi : ∀ j ∈ s, 0 ≤ phi j) (hD : ∀ j ∈ s, (D j).IsPositive) :
    (∑ j ∈ s, phi j • D j).IsPositive := by
  apply ContinuousLinearMap.isPositive_sum
  intro j hj
  exact (hD j hj).smul_of_nonneg (hphi j hj)

end RegularPointCoordinates

end OAI
