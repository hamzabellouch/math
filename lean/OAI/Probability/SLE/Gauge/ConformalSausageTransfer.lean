import OAI.Probability.SLE.SausageScaling

namespace OAI

/-!
Deterministic conformal area and sausage transfer in `rc:compact-sausage-transfer`
of *An explicit exact Hausdorff gauge for SLE*. The local patches below may
depend on the sausage point; their union need not be convex.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal

namespace SLEExactGauge

lemma complex_derivative_real_det (a : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).det = ‖a‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

/-- An injective complex differentiable map with derivative bounded below
expands area by at least the square of that lower bound. -/
theorem conformal_area_image_lower
    {F F' : ℂ → ℂ} {S : Set ℂ} (hS : MeasurableSet S)
    (hinj : InjOn F S) (hF : ∀ z ∈ S, HasDerivAt F (F' z) z)
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ z ∈ S, c ≤ ‖F' z‖) :
    ENNReal.ofReal (c ^ 2) * volume S ≤ volume (F '' S) := by
  have harea := lintegral_abs_det_fderiv_eq_addHaar_image volume hS
    (fun z hz => ((hF z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj
  rw [← harea, ← setLIntegral_const]
  apply setLIntegral_mono' hS
  intro z hz
  rw [complex_derivative_real_det, abs_of_nonneg (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc (hbound z hz) 2)

/-- A point in a small sausage and its witnessing trace point only need to
lie in one common Lipschitz patch. No global convexity is assumed. -/
theorem sourceSausage_image_subset_of_lipschitz_patches
    (F : ℂ → ℂ) (γ : ℝ≥0 → ℂ) (s t : ℝ≥0)
    {v ell : ℝ} (hv : 0 < v) (C : ℝ≥0) (hscale : (C : ℝ) * ell ≤ 1)
    (hpatch : ∀ z ∈ sourceSausageSet γ s t (ell * v),
      ∃ u ∈ Icc s t, dist z (γ u) < ell * v ∧
        ∃ K : Set ℂ, z ∈ K ∧ γ u ∈ K ∧ LipschitzOnWith C F K) :
    F '' sourceSausageSet γ s t (ell * v) ⊆
      sourceSausageSet (fun u => F (γ u)) s t v := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨u, hu, hdist, K, hzK, huK, hLip⟩ := hpatch z hz
  refine ⟨u, hu, (hLip.dist_le_mul z hzK (γ u) huK).trans_lt ?_⟩
  by_cases hC : C = 0
  · simpa only [hC, NNReal.coe_zero, zero_mul] using hv
  · have hCpos : 0 < (C : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hC)
    calc
      (C : ℝ) * dist z (γ u) < (C : ℝ) * (ell * v) :=
        mul_lt_mul_of_pos_left hdist hCpos
      _ ≤ v := by nlinarith [mul_le_mul_of_nonneg_right hscale hv.le]

/-- Complex derivative bounds on convex patches give the local Lipschitz
comparison required to send the small sausage into the physical sausage. -/
theorem sourceSausage_image_subset_of_derivative_patches
    (F F' : ℂ → ℂ) (γ : ℝ≥0 → ℂ) (s t : ℝ≥0)
    {v ell : ℝ} (hv : 0 < v) (C : ℝ≥0) (hscale : (C : ℝ) * ell ≤ 1)
    (hpatch : ∀ z ∈ sourceSausageSet γ s t (ell * v),
      ∃ u ∈ Icc s t, dist z (γ u) < ell * v ∧
        ∃ K : Set ℂ, Convex ℝ K ∧ z ∈ K ∧ γ u ∈ K ∧
          (∀ w ∈ K, HasDerivWithinAt F (F' w) K w) ∧
          (∀ w ∈ K, ‖F' w‖₊ ≤ C)) :
    F '' sourceSausageSet γ s t (ell * v) ⊆
      sourceSausageSet (fun u => F (γ u)) s t v := by
  apply sourceSausage_image_subset_of_lipschitz_patches F γ s t hv C hscale
  intro z hz
  obtain ⟨u, hu, hdist, K, hconv, hzK, huK, hF, hbound⟩ := hpatch z hz
  exact ⟨u, hu, hdist, K, hzK, huK,
    hconv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le hF hbound⟩

/-- Normalize the area inequality at physical mesh `v`, expressing the
small-mesh mass at `ell * v`. This is the exact factor in the manuscript. -/
theorem normalized_conformal_area_lower
    {F F' : ℂ → ℂ} {S A : Set ℂ} (hS : MeasurableSet S)
    (hinj : InjOn F S) (hF : ∀ z ∈ S, HasDerivAt F (F' z) z)
    {c v ell p : ℝ} (hc : 0 ≤ c) (hv : 0 < v) (hell : 0 < ell)
    (hbound : ∀ z ∈ S, c ≤ ‖F' z‖) (himage : F '' S ⊆ A) :
    ENNReal.ofReal (c ^ 2 * ell ^ p) *
        (ENNReal.ofReal ((ell * v) ^ (-p)) * volume S) ≤
      ENNReal.ofReal (v ^ (-p)) * volume A := by
  have harea := (conformal_area_image_lower hS hinj hF hc hbound).trans
    (measure_mono himage)
  have hcoeff : c ^ 2 * ell ^ p * (ell * v) ^ (-p) = v ^ (-p) * c ^ 2 := by
    rw [Real.mul_rpow hell.le hv.le]
    calc
      _ = c ^ 2 * (ell ^ p * ell ^ (-p)) * v ^ (-p) := by ring
      _ = v ^ (-p) * c ^ 2 := by rw [← Real.rpow_add hell, add_neg_cancel, Real.rpow_zero]; ring
  have he : ENNReal.ofReal (c ^ 2 * ell ^ p) * ENNReal.ofReal ((ell * v) ^ (-p)) =
      ENNReal.ofReal (v ^ (-p)) * ENNReal.ofReal (c ^ 2) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg c) (Real.rpow_nonneg hell.le _)),
      hcoeff, ENNReal.ofReal_mul (Real.rpow_nonneg hv.le _)]
  rw [← mul_assoc, he, mul_assoc]
  exact mul_le_mul' le_rfl harea

/-- The physical sausage inside the retained middle region receives at
least `c² ell^p` times the small-mesh normalized mass. -/
theorem sourceSausageMass_conformal_transfer
    (κ : ℝ) (F F' : ℂ → ℂ) (γ : ℝ≥0 → ℂ) (s t : ℝ≥0)
    (R : Set ℂ) {c v ell : ℝ} (hc : 0 ≤ c) (hv : 0 < v) (hell : 0 < ell)
    (hinj : InjOn F (sourceSausageSet γ s t (ell * v)))
    (hF : ∀ z ∈ sourceSausageSet γ s t (ell * v), HasDerivAt F (F' z) z)
    (hbound : ∀ z ∈ sourceSausageSet γ s t (ell * v), c ≤ ‖F' z‖)
    (C : ℝ≥0) (hscale : (C : ℝ) * ell ≤ 1)
    (hregion : F '' sourceSausageSet γ s t (ell * v) ⊆ R)
    (hpatch : ∀ z ∈ sourceSausageSet γ s t (ell * v),
      ∃ u ∈ Icc s t, dist z (γ u) < ell * v ∧
        ∃ K : Set ℂ, Convex ℝ K ∧ z ∈ K ∧ γ u ∈ K ∧
          (∀ w ∈ K, HasDerivWithinAt F (F' w) K w) ∧
          (∀ w ∈ K, ‖F' w‖₊ ≤ C)) :
    ENNReal.ofReal (c ^ 2 * ell ^ codimension κ) *
        sourceSausageMass κ γ s t (ell * v) ≤
      ENNReal.ofReal (v ^ (-codimension κ)) *
        volume (R ∩ sourceSausageSet (fun u => F (γ u)) s t v) := by
  apply normalized_conformal_area_lower (source_sausage_isOpen γ s t (ell * v)).measurableSet
    hinj hF hc hv hell hbound
  exact subset_inter hregion
    (sourceSausage_image_subset_of_derivative_patches F F' γ s t hv C hscale hpatch)

end SLEExactGauge

end

end OAI
