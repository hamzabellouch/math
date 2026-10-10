import OAI.Geometry.RCD.Coordinates.FrozenNorms
import OAI.Geometry.RCD.Coordinates.FieldEstimates

namespace OAI

/-!
# Directional estimates for finite patch fields

The finite set is the set of active patches at the point under consideration.
All metric norms are frozen using a continuous linear equivalence `T`.
The hypotheses are the individual displacement energies, cutoff derivative
bounds, overlap bound, and positive mass bounds; no field estimate is assumed.
-/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unweighted mass of the active patches. -/
def patchMass (s : Finset ι) (D : ι → E →L[ℝ] E) : E →L[ℝ] E :=
  ∑ j ∈ s, D j

/-- The principal part of the derivative of the patch field. -/
def patchPrincipal (s : Finset ι) (phi : ι → ℝ) (D : ι → E →L[ℝ] E) :
    E →L[ℝ] E := ∑ j ∈ s, phi j • D j

/-- The error produced by differentiating the cutoff functions. -/
def patchCutoffError (s : Finset ι) (D : ι → E →L[ℝ] E)
    (w : ι → E) (a : ι → ℝ) : E := ∑ j ∈ s, a j • D j (w j)

theorem patchMass_isPositive (s : Finset ι) (D : ι → E →L[ℝ] E)
    (hD : ∀ j ∈ s, (D j).IsPositive) : (patchMass s D).IsPositive := by
  exact ContinuousLinearMap.isPositive_sum s hD

theorem inner_patchMass (s : Finset ι) (D : ι → E →L[ℝ] E) (x : E) :
    ⟪x, patchMass s D x⟫_ℝ = ∑ j ∈ s, ⟪x, D j x⟫_ℝ := by
  simp [patchMass, inner_sum]

/-- Each positive patch is bounded above by the total positive mass. -/
theorem patch_form_le_mass (s : Finset ι) (D : ι → E →L[ℝ] E)
    (hD : ∀ j ∈ s, (D j).IsPositive) {j : ι} (hj : j ∈ s) (x : E) :
    ⟪x, D j x⟫_ℝ ≤ ⟪x, patchMass s D x⟫_ℝ := by
  rw [inner_patchMass]
  exact Finset.single_le_sum (fun k hk => (hD k hk).inner_nonneg_right x) hj

/-- Nonnegative cutoffs bounded by one give `0 ≤ S ≤ Z`. -/
theorem patchPrincipal_form_le_mass (s : Finset ι) (phi : ι → ℝ)
    (D : ι → E →L[ℝ] E) (hD : ∀ j ∈ s, (D j).IsPositive)
    (hphi : ∀ j ∈ s, phi j ≤ 1) (x : E) :
    ⟪x, patchPrincipal s phi D x⟫_ℝ ≤ ⟪x, patchMass s D x⟫_ℝ := by
  simp only [patchPrincipal, patchMass, sum_apply, smul_apply, inner_sum,
    inner_smul_right]
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_of_le_one_left ((hD j hj).inner_nonneg_right x) (hphi j hj)

variable [CompleteSpace E]

/-- The cumulative smallness `Z ≤ epsilon H` gives the sharp principal bound.
Individual smallness of each patch alone is not used as a substitute for this
cumulative hypothesis. -/
theorem patchPrincipal_frozen_norm_le (T : E ≃L[ℝ] E) (s : Finset ι)
    (phi : ι → ℝ) (D : ι → E →L[ℝ] E) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hD : ∀ j ∈ s, (D j).IsPositive)
    (hphi0 : ∀ j ∈ s, 0 ≤ phi j) (hphi1 : ∀ j ∈ s, phi j ≤ 1)
    (hZ : ∀ x, ⟪x, patchMass s D x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2) (xi : E) :
    ‖(T.symm : E →L[ℝ] E).adjoint (patchPrincipal s phi D xi)‖ ≤
      Real.sqrt epsilon * Real.sqrt ⟪xi, patchMass s D xi⟫_ℝ := by
  have hS := patch_principal_isPositive s phi D hphi0 hD
  have hle := patchPrincipal_form_le_mass s phi D hD hphi1
  have h := frozen_positive_form_norm_le T hS hepsilon (fun x => (hle x).trans (hZ x)) xi
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hle xi))
    (Real.sqrt_nonneg _))

/-- A weighted finite patch sum in the dual metric. -/
theorem frozen_patch_weighted_value_le (T : E ≃L[ℝ] E) (s : Finset ι)
    (D : ι → E →L[ℝ] E) (w : ι → E) (a : ι → ℝ) {N : ℕ}
    {epsilon C r energy A : ℝ} (hN : s.card ≤ N)
    (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (henergy : 0 ≤ energy) (hA : 0 ≤ A)
    (hD : ∀ j ∈ s, (D j).IsPositive)
    (hsmall : ∀ j ∈ s, ∀ x, ⟪x, D j x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2)
    (hw : ∀ j ∈ s, ⟪w j, D j (w j)⟫_ℝ ≤ C * r ^ 2 * energy)
    (ha : ∀ j ∈ s, |a j| ≤ A) :
    ‖(T.symm : E →L[ℝ] E).adjoint (patchCutoffError s D w a)‖ ≤
      (N : ℝ) * A * (Real.sqrt epsilon * Real.sqrt C * r * Real.sqrt energy) := by
  rw [patchCutoffError, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ j ∈ s, ‖(T.symm : E →L[ℝ] E).adjoint (a j • D j (w j))‖
        ≤ ∑ _j ∈ s, A * (Real.sqrt epsilon * Real.sqrt C * r * Real.sqrt energy) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [map_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (ha j hj)
        (frozen_positive_form_value_le T (hD j hj) hepsilon hC hr henergy
          (hsmall j hj) (w j) (hw j hj)) (norm_nonneg _) hA
    _ = (s.card : ℝ) * (A * (Real.sqrt epsilon * Real.sqrt C * r * Real.sqrt energy)) := by
      simp
    _ ≤ (N : ℝ) * (A * (Real.sqrt epsilon * Real.sqrt C * r * Real.sqrt energy)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (by positivity)
    _ = _ := by ring

/-- The normalized value estimate `re:field-value`. -/
theorem patchField_frozen_value_le (T : E ≃L[ℝ] E) (s : Finset ι)
    (phi : ι → E → ℝ) (D : ι → E →L[ℝ] E) (c : ι → E) (P : E) {N : ℕ}
    {epsilon C r energy : ℝ} (hN : s.card ≤ N)
    (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C) (hr : 0 < r) (henergy : 0 ≤ energy)
    (hD : ∀ j ∈ s, (D j).IsPositive)
    (hsmall : ∀ j ∈ s, ∀ x, ⟪x, D j x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2)
    (hw : ∀ j ∈ s, ⟪P - c j, D j (P - c j)⟫_ℝ ≤ C * r ^ 2 * energy)
    (hphi : ∀ j ∈ s, |phi j P| ≤ 1) :
    ‖(T.symm : E →L[ℝ] E).adjoint (patchField s phi D c P)‖ / r ≤
      (N : ℝ) * Real.sqrt C * Real.sqrt epsilon * Real.sqrt energy := by
  apply (div_le_iff₀ hr).2
  have h := frozen_patch_weighted_value_le T s D (fun j => P - c j)
    (fun j => phi j P) hN hepsilon hC hr.le henergy zero_le_one hD hsmall hw hphi
  change ‖(T.symm : E →L[ℝ] E).adjoint (patchField s phi D c P)‖ ≤ _ at h
  convert h using 1
  ring

/-- The dual norm estimate for the linear cutoff error. -/
theorem patchCutoffError_frozen_norm_le (T : E ≃L[ℝ] E) (s : Finset ι)
    (D : ι → E →L[ℝ] E) (w : ι → E) (a : ι → ℝ) (xi : E) {N : ℕ}
    {epsilon C K r energy : ℝ} (hN : s.card ≤ N)
    (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hr : 0 < r) (henergy : 0 ≤ energy)
    (hD : ∀ j ∈ s, (D j).IsPositive)
    (hsmall : ∀ j ∈ s, ∀ x, ⟪x, D j x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2)
    (hw : ∀ j ∈ s, ⟪w j, D j (w j)⟫_ℝ ≤ C * r ^ 2 * energy)
    (ha : ∀ j ∈ s, |a j| ≤ K / r * ‖T xi‖) :
    ‖(T.symm : E →L[ℝ] E).adjoint (patchCutoffError s D w a)‖ ≤
      (N : ℝ) * K * Real.sqrt C * Real.sqrt epsilon * Real.sqrt energy * ‖T xi‖ := by
  have h := frozen_patch_weighted_value_le T s D w a hN hepsilon hC hr.le henergy
    (A := K / r * ‖T xi‖) (by positivity) hD hsmall hw ha
  convert h using 1
  field_simp [ne_of_gt hr]

omit [CompleteSpace E] in
/-- Bounded overlap controls the total displacement energy. -/
theorem sqrt_patch_energy_sum_le (s : Finset ι) (D : ι → E →L[ℝ] E)
    (w : ι → E) {N : ℕ} {C r energy : ℝ} (hN : s.card ≤ N)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (henergy : 0 ≤ energy)
    (hD : ∀ j ∈ s, (D j).IsPositive)
    (hw : ∀ j ∈ s, ⟪w j, D j (w j)⟫_ℝ ≤ C * r ^ 2 * energy) :
    Real.sqrt (∑ j ∈ s, ⟪w j, D j (w j)⟫_ℝ) ≤
      Real.sqrt ((N : ℝ) * C) * r * Real.sqrt energy := by
  have hsum0 : 0 ≤ ∑ j ∈ s, ⟪w j, D j (w j)⟫_ℝ :=
    Finset.sum_nonneg (fun j hj => (hD j hj).inner_nonneg_right _)
  have hsum : (∑ j ∈ s, ⟪w j, D j (w j)⟫_ℝ) ≤ (N : ℝ) * C * r ^ 2 * energy := by
    calc
      _ ≤ ∑ _j ∈ s, C * r ^ 2 * energy := Finset.sum_le_sum hw
      _ = (s.card : ℝ) * (C * r ^ 2 * energy) := by simp
      _ ≤ (N : ℝ) * (C * r ^ 2 * energy) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (by positivity)
      _ = _ := by ring
  have hroot : (Real.sqrt ((N : ℝ) * C) * r * Real.sqrt energy) ^ 2 =
      (N : ℝ) * C * r ^ 2 * energy := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt henergy]
  have hnonneg : 0 ≤ Real.sqrt ((N : ℝ) * C) * r * Real.sqrt energy := by positivity
  nlinarith [Real.sq_sqrt hsum0, Real.sqrt_nonneg
    (∑ j ∈ s, ⟪w j, D j (w j)⟫_ℝ)]

omit [CompleteSpace E] in
/-- The sharp diagonal estimate retains the directional mass `Z[xi]`.
It does not replace this mass by a bound in terms of the whole source metric. -/
theorem patchCutoffError_diagonal_le (T : E ≃L[ℝ] E) (s : Finset ι)
    (D : ι → E →L[ℝ] E) (w : ι → E) (a : ι → ℝ) (xi : E) {N : ℕ}
    {C K r energy : ℝ} (hN : s.card ≤ N) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hr : 0 < r) (henergy : 0 ≤ energy)
    (hD : ∀ j ∈ s, (D j).IsPositive)
    (hw : ∀ j ∈ s, ⟪w j, D j (w j)⟫_ℝ ≤ C * r ^ 2 * energy)
    (ha : ∀ j ∈ s, |a j| ≤ K / r * ‖T xi‖) :
    |⟪xi, patchCutoffError s D w a⟫_ℝ| ≤
      K * Real.sqrt ((N : ℝ) * C) *
        Real.sqrt ⟪xi, patchMass s D xi⟫_ℝ * Real.sqrt energy * ‖T xi‖ := by
  have h := patch_error_inner_le s D w a xi (K := K / r * ‖T xi‖)
    (by positivity) hD ha
  rw [← inner_patchMass] at h
  have henergySum := sqrt_patch_energy_sum_le s D w hN hC hr.le henergy hD hw
  have h' := h.trans (mul_le_mul_of_nonneg_left henergySum
    (show 0 ≤ K / r * ‖T xi‖ * Real.sqrt ⟪xi, patchMass s D xi⟫_ℝ by positivity))
  change |⟪xi, patchCutoffError s D w a⟫_ℝ| ≤ _ at h'
  convert h' using 1
  field_simp [ne_of_gt hr]

omit [CompleteSpace E] in
/-- The bounds above apply to the actual derivative, with the exact principal
and cutoff-error decomposition supplied by differentiation. -/
theorem fderiv_patchField_apply (s : Finset ι) (phi : ι → E → ℝ)
    (dphi : ι → E →L[ℝ] ℝ) (D : ι → E →L[ℝ] E) (c : ι → E) (P xi : E)
    (hphi : ∀ j ∈ s, HasFDerivAt (phi j) (dphi j) P) :
    fderiv ℝ (patchField s phi D c) P xi =
      patchPrincipal s (fun j => phi j P) D xi +
        patchCutoffError s D (fun j => P - c j) (fun j => dphi j xi) := by
  rw [(hasFDerivAt_patchField s phi dphi D c P hphi).fderiv]
  simp [patchPrincipal, patchCutoffError, Finset.sum_add_distrib]

end RegularPointCoordinates

end

end OAI
