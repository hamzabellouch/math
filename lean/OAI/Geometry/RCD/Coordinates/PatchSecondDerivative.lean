import OAI.Geometry.RCD.Coordinates.PatchDirectionalBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-!
# The second directional derivative of the patch field

This proves the actual derivative formula and the frozen dual-norm bound
in `re:field-second`.  The only nonzero terms differentiate the cutoff twice,
or differentiate the cutoff and the affine factor once each.
-/

open Filter
open scoped Topology BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

section Calculus

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The second directional derivative of a cutoff times an affine map. -/
theorem cutoff_affine_second_directional (phi : E → ℝ) (D : E →L[ℝ] F)
    (c P xi : E) (hphi : ContDiffAt ℝ 2 phi P) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => phi z • D (z - c)) y xi) P xi =
      fderiv ℝ (fun y => fderiv ℝ phi y xi) P xi • D (P - c) +
        (2 * fderiv ℝ phi P xi) • D xi := by
  have hdphi := hphi.differentiableAt (by norm_num)
  have hddphi := (hphi.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)
  have hdxi := hddphi.hasFDerivAt.clm_apply (hasFDerivAt_const xi P)
  have hD : HasFDerivAt (fun y => D (y - c)) D P := by
    simpa [Function.comp_def] using D.hasFDerivAt.comp P ((hasFDerivAt_id P).sub_const c)
  have hterm := (hdphi.hasFDerivAt.smul_const (D xi)).add (hdxi.fun_smul hD)
  have hevent : ∀ᶠ y in 𝓝 P, ContDiffAt ℝ 2 phi y := hphi.eventually (by norm_num)
  have heq : (fun y => phi y • D xi + fderiv ℝ phi y xi • D (y - c)) =ᶠ[𝓝 P]
      (fun y => fderiv ℝ (fun z => phi z • D (z - c)) y xi) := by
    filter_upwards [hevent] with y hy
    have hDy : HasFDerivAt (fun z => D (z - c)) D y := by
      simpa [Function.comp_def] using D.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const c)
    rw [((hy.differentiableAt (by norm_num)).hasFDerivAt.fun_smul hDy).fderiv]
    simp
  have hactual := hterm.congr_of_eventuallyEq heq.symm
  rw [hactual.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.comp_apply, zero_apply, map_zero,
    zero_add, ContinuousLinearMap.flip_apply]
  have hdxi_apply : fderiv ℝ (fun y => fderiv ℝ phi y xi) P xi =
      fderiv ℝ (fderiv ℝ phi) P xi xi := by
    rw [hdxi.fderiv]
    simp
  rw [hdxi_apply]
  module

/-- Finite sums commute with the actual second directional derivative. -/
theorem second_directional_finset_sum (s : Finset ι) (f : ι → E → F) (P xi : E)
    (hf : ∀ j ∈ s, ContDiffAt ℝ 2 (f j) P) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => ∑ j ∈ s, f j z) y xi) P xi =
      ∑ j ∈ s, fderiv ℝ (fun y => fderiv ℝ (f j) y xi) P xi := by
  have hdiff : ∀ j ∈ s, DifferentiableAt ℝ (fun y => fderiv ℝ (f j) y xi) P := by
    intro j hj
    exact ((hf j hj).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.clm_apply (differentiableAt_const xi)
  have hevent : ∀ᶠ y in 𝓝 P, ∀ j ∈ s, ContDiffAt ℝ 2 (f j) y :=
    (eventually_all_finset s).2 (fun j hj => (hf j hj).eventually (by norm_num))
  have heq : (fun y => ∑ j ∈ s, fderiv ℝ (f j) y xi) =ᶠ[𝓝 P]
      (fun y => fderiv ℝ (fun z => ∑ j ∈ s, f j z) y xi) := by
    filter_upwards [hevent] with y hy
    rw [fderiv_fun_sum (fun j hj => (hy j hj).differentiableAt (by norm_num))]
    simp
  have hactual := (HasFDerivAt.fun_sum (fun j hj => (hdiff j hj).hasFDerivAt)).congr_of_eventuallyEq
    heq.symm
  rw [hactual.fderiv]
  simp

end Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The full finite-patch formula from local twice continuous differentiability
of the cutoff functions. -/
theorem patchField_second_directional (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (P xi : E)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ 2 (phi j) P) :
    fderiv ℝ (fun y => fderiv ℝ (patchField s phi D c) y xi) P xi =
      ∑ j ∈ s, (fderiv ℝ (fun y => fderiv ℝ (phi j) y xi) P xi • D j (P - c j) +
        (2 * fderiv ℝ (phi j) P xi) • D j xi) := by
  have hterm : ∀ j ∈ s, ContDiffAt ℝ 2 (fun z => phi j z • D j (z - c j)) P := by
    intro j hj
    exact (hphi j hj).smul ((D j).contDiff.contDiffAt.comp P
      (contDiffAt_id.sub contDiffAt_const))
  change fderiv ℝ (fun y => fderiv ℝ
    (fun z => ∑ j ∈ s, phi j z • D j (z - c j)) y xi) P xi = _
  rw [second_directional_finset_sum s _ P xi hterm]
  exact Finset.sum_congr rfl (fun j hj => cutoff_affine_second_directional
    (phi j) (D j) (c j) P xi (hphi j hj))

variable [CompleteSpace E]

/-- A derivative-weighted sum of mass values retains the square root of
the total directional mass. -/
theorem frozen_patch_directional_sum_le (T : E ≃L[ℝ] E) (s : Finset ι)
    (D : ι → E →L[ℝ] E) (a : ι → ℝ) (xi : E) {N : ℕ} {epsilon A : ℝ}
    (hN : s.card ≤ N) (hepsilon : 0 ≤ epsilon) (hA : 0 ≤ A)
    (hD : ∀ j ∈ s, (D j).IsPositive)
    (hZ : ∀ x, ⟪x, patchMass s D x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2)
    (ha : ∀ j ∈ s, |a j| ≤ A) :
    ‖(T.symm : E →L[ℝ] E).adjoint (patchCutoffError s D (fun _ => xi) a)‖ ≤
      A * Real.sqrt epsilon * Real.sqrt (N : ℝ) *
        Real.sqrt ⟪xi, patchMass s D xi⟫_ℝ := by
  have hsmall : ∀ j ∈ s, ∀ x, ⟪x, D j x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2 :=
    fun j hj x => (patch_form_le_mass s D hD hj x).trans (hZ x)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => (1 : ℝ))
    (fun j => Real.sqrt ⟪xi, D j xi⟫_ℝ)
  have hsq : (∑ j ∈ s, (Real.sqrt ⟪xi, D j xi⟫_ℝ) ^ 2) =
      ⟪xi, patchMass s D xi⟫_ℝ := by
    rw [inner_patchMass]
    exact Finset.sum_congr rfl (fun j hj => Real.sq_sqrt ((hD j hj).inner_nonneg_right xi))
  rw [hsq] at hcs
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsum : (∑ j ∈ s, Real.sqrt ⟪xi, D j xi⟫_ℝ) ≤
      Real.sqrt (N : ℝ) * Real.sqrt ⟪xi, patchMass s D xi⟫_ℝ :=
    hcs.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast hN))
      (Real.sqrt_nonneg _))
  calc
    _ ≤ ∑ j ∈ s, |a j| * (Real.sqrt epsilon * Real.sqrt ⟪xi, D j xi⟫_ℝ) :=
      frozen_positive_patch_sum_norm_le T s D (fun _ => xi) a hepsilon hD hsmall
    _ ≤ ∑ j ∈ s, A * (Real.sqrt epsilon * Real.sqrt ⟪xi, D j xi⟫_ℝ) := by
      exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (ha j hj) (by positivity))
    _ = A * Real.sqrt epsilon * ∑ j ∈ s, Real.sqrt ⟪xi, D j xi⟫_ℝ := by
      simp only [mul_assoc, Finset.mul_sum]
    _ ≤ A * Real.sqrt epsilon * (Real.sqrt (N : ℝ) * Real.sqrt ⟪xi, patchMass s D xi⟫_ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- The second derivative estimate with the small factor retained. -/
theorem patchField_second_directional_frozen_le_sqrt (T : E ≃L[ℝ] E) (s : Finset ι)
    (phi : ι → E → ℝ) (D : ι → E →L[ℝ] E) (c : ι → E) (P xi : E) {N : ℕ}
    {epsilon C K r energy : ℝ} (hN : s.card ≤ N)
    (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hr : 0 < r) (henergy : 0 ≤ energy)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ 2 (phi j) P)
    (hD : ∀ j ∈ s, (D j).IsPositive)
    (hZ : ∀ x, ⟪x, patchMass s D x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2)
    (hw : ∀ j ∈ s, ⟪P - c j, D j (P - c j)⟫_ℝ ≤ C * r ^ 2 * energy)
    (hfirst : ∀ j ∈ s, |fderiv ℝ (phi j) P xi| ≤ K / r * ‖T xi‖)
    (hsecond : ∀ j ∈ s, |fderiv ℝ (fun y => fderiv ℝ (phi j) y xi) P xi| ≤
      K / r ^ 2 * ‖T xi‖ ^ 2) :
    r * ‖(T.symm : E →L[ℝ] E).adjoint
      (fderiv ℝ (fun y => fderiv ℝ (patchField s phi D c) y xi) P xi)‖ ≤
      Real.sqrt epsilon * ((N : ℝ) * K * Real.sqrt C * Real.sqrt energy * ‖T xi‖ ^ 2 +
        2 * K * Real.sqrt (N : ℝ) * Real.sqrt ⟪xi, patchMass s D xi⟫_ℝ * ‖T xi‖) := by
  let a : ι → ℝ := fun j => fderiv ℝ (phi j) P xi
  let b : ι → ℝ := fun j => fderiv ℝ (fun y => fderiv ℝ (phi j) y xi) P xi
  have hsmall : ∀ j ∈ s, ∀ x, ⟪x, D j x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2 :=
    fun j hj x => (patch_form_le_mass s D hD hj x).trans (hZ x)
  have hb := frozen_patch_weighted_value_le T s D (fun j => P - c j) b hN
    hepsilon hC hr.le henergy (A := K / r ^ 2 * ‖T xi‖ ^ 2) (by positivity)
    hD hsmall hw hsecond
  have ha := frozen_patch_directional_sum_le T s D a xi hN hepsilon
    (A := K / r * ‖T xi‖) (by positivity) hD hZ hfirst
  have hformula : fderiv ℝ (fun y => fderiv ℝ (patchField s phi D c) y xi) P xi =
      patchCutoffError s D (fun j => P - c j) b +
        (2 : ℝ) • patchCutoffError s D (fun _ => xi) a := by
    rw [patchField_second_directional s phi D c P xi hphi]
    simp [patchCutoffError, a, b, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]
  rw [hformula, map_add, map_smul]
  calc
    _ ≤ r * (‖(T.symm : E →L[ℝ] E).adjoint
          (patchCutoffError s D (fun j => P - c j) b)‖ +
        2 * ‖(T.symm : E →L[ℝ] E).adjoint (patchCutoffError s D (fun _ => xi) a)‖) := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        using norm_add_le ((T.symm : E →L[ℝ] E).adjoint
          (patchCutoffError s D (fun j => P - c j) b))
          ((2 : ℝ) • (T.symm : E →L[ℝ] E).adjoint (patchCutoffError s D (fun _ => xi) a))
    _ ≤ r * ((N : ℝ) * (K / r ^ 2 * ‖T xi‖ ^ 2) *
          (Real.sqrt epsilon * Real.sqrt C * r * Real.sqrt energy) +
        2 * ((K / r * ‖T xi‖) * Real.sqrt epsilon * Real.sqrt (N : ℝ) *
          Real.sqrt ⟪xi, patchMass s D xi⟫_ℝ)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hb (mul_le_mul_of_nonneg_left ha (by norm_num))) hr.le
    _ = _ := by field_simp [ne_of_gt hr]

/-- With `epsilon ≤ 1`, the small factor may be dropped, giving the two
terms in `re:field-second` with explicit overlap and cutoff constants. -/
theorem patchField_second_directional_frozen_le (T : E ≃L[ℝ] E) (s : Finset ι)
    (phi : ι → E → ℝ) (D : ι → E →L[ℝ] E) (c : ι → E) (P xi : E) {N : ℕ}
    {epsilon C K r energy : ℝ} (hN : s.card ≤ N)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hr : 0 < r) (henergy : 0 ≤ energy)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ 2 (phi j) P)
    (hD : ∀ j ∈ s, (D j).IsPositive)
    (hZ : ∀ x, ⟪x, patchMass s D x⟫_ℝ ≤ epsilon * ‖T x‖ ^ 2)
    (hw : ∀ j ∈ s, ⟪P - c j, D j (P - c j)⟫_ℝ ≤ C * r ^ 2 * energy)
    (hfirst : ∀ j ∈ s, |fderiv ℝ (phi j) P xi| ≤ K / r * ‖T xi‖)
    (hsecond : ∀ j ∈ s, |fderiv ℝ (fun y => fderiv ℝ (phi j) y xi) P xi| ≤
      K / r ^ 2 * ‖T xi‖ ^ 2) :
    r * ‖(T.symm : E →L[ℝ] E).adjoint
      (fderiv ℝ (fun y => fderiv ℝ (patchField s phi D c) y xi) P xi)‖ ≤
      (N : ℝ) * K * Real.sqrt C * Real.sqrt energy * ‖T xi‖ ^ 2 +
        2 * K * Real.sqrt (N : ℝ) * Real.sqrt ⟪xi, patchMass s D xi⟫_ℝ * ‖T xi‖ := by
  have hsqrt : Real.sqrt epsilon ≤ 1 := by
    nlinarith [Real.sq_sqrt hepsilon, Real.sqrt_nonneg epsilon]
  exact (patchField_second_directional_frozen_le_sqrt T s phi D c P xi hN
    hepsilon hC hK hr henergy hphi hD hZ hw hfirst hsecond).trans
      (mul_le_of_le_one_left (by positivity) hsqrt)

end RegularPointCoordinates

end

end OAI
