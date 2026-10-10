import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPolarL2

namespace OAI

/-! # Angular projection preserves the radial L² condition

This applies to every square-integrable angular test, hence in particular
to each normalized spherical harmonic.  No angular eigenfunction equation
is assumed or used by the measure-theoretic estimate.
-/

open MeasureTheory

namespace DefocusingNLS

private theorem norm_sq_toLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℂ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := real_inner_self_eq_norm_sq (hf.toLp f)
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- Cauchy--Schwarz in the angular variable, with its exact L² constant. -/
theorem angular_integral_norm_sq_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (h f : α → ℂ) (hh : MemLp h 2 μ) (hf : MemLp f 2 μ) :
    ‖∫ x, inner ℂ (h x) (f x) ∂μ‖ ^ 2 ≤
      (∫ x, ‖h x‖ ^ 2 ∂μ) * (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  have heq : (∫ x, inner ℂ (h x) (f x) ∂μ) =
      inner ℂ (hh.toLp h) (hf.toLp f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp, hf.coeFn_toLp] with x hx hy
    rw [hx, hy]
  rw [heq, ← norm_sq_toLp μ h hh, ← norm_sq_toLp μ f hf]
  calc
    _ ≤ (‖hh.toLp h‖ * ‖hf.toLp f‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
    _ = _ := by ring

/-- A fixed L² angular projection of an L² polar field is in L²(r^11 dr). -/
theorem memLp_angularProjection (h : PhysicalUnitSphere → ℂ)
    (hh : MemLp h 2 physicalSphereMeasure)
    (F : PhysicalUnitSphere × PhysicalPositiveRadius → ℂ)
    (hF : MemLp F 2 physicalPolarMeasure) :
    MemLp (fun r => ∫ ω, inner ℂ (h ω) (F (ω, r)) ∂physicalSphereMeasure)
      2 physicalRadiusMeasure := by
  have hsq : Integrable (fun p => ‖F p‖ ^ 2) physicalPolarMeasure :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hmeas : AEStronglyMeasurable
      (fun p : PhysicalUnitSphere × PhysicalPositiveRadius =>
        inner ℂ (h p.1) (F p)) physicalPolarMeasure :=
    hh.aestronglyMeasurable.comp_fst.inner hF.aestronglyMeasurable
  have hproj := hmeas.prod_swap.integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hproj).mpr
  apply (hsq.integral_norm_prod_right.const_mul
    (∫ ω, ‖h ω‖ ^ 2 ∂physicalSphereMeasure)).mono'
  · exact hproj.norm.pow 2
  filter_upwards [hF.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with r hmr hir
  have hr : MemLp (fun ω => F (ω, r)) 2 physicalSphereMeasure :=
    (memLp_two_iff_integrable_sq_norm hmr).mpr hir
  simpa only [Function.comp_def, Prod.swap_prod_mk, Real.norm_eq_abs, abs_pow, abs_norm, Pi.pow_apply,
    Real.norm_of_nonneg (sq_nonneg _)] using
    angular_integral_norm_sq_le physicalSphereMeasure h (fun ω => F (ω, r)) hh hr

/-- The angular component of each completed Cartesian top derivative satisfies
exactly the radial weighted L² condition used in spectral exclusion. -/
theorem homogeneousPolarDerivative_angular_memLp (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12)
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (u : HomogeneousY a N) :
    MemLp (fun r => ∫ ω, inner ℂ (h ω)
      (homogeneousPolarDerivative a N ha ha1 hk j u (ω, r)) ∂physicalSphereMeasure)
      2 physicalRadiusMeasure :=
  memLp_angularProjection h hh _ (Lp.memLp _)

end DefocusingNLS

end OAI
