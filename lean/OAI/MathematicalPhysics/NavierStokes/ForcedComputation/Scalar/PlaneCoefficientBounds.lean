import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.SpatialParameterDerivatives
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Uniform bounds and time moduli for periodic and compactly supported coefficients. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped ContDiff NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
theorem planePeriodic_bound_on {f : ℝ × Plane → F} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b ×ˢ (univ : Set Plane)))
    (hp : ∀ t ∈ Icc a b, PlanePeriodic (fun x => f (t,x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x, ‖f (t,x)‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod
    (isCompact_Icc : IsCompact (Icc (0 : Plane) (fun _ => 1)))).exists_bound_of_continuousOn
      (hf.mono (fun p hp => ⟨hp.1, mem_univ _⟩))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x
  let y : Plane := fun j => Int.fract (x j)
  have hy : y ∈ Icc (0 : Plane) (fun _ => 1) :=
    ⟨fun j => Int.fract_nonneg _, fun j => (Int.fract_lt_one _).le⟩
  have he : y + (fun j => ((⌊x j⌋ : ℤ) : ℝ)) = x := by
    ext j
    exact Int.fract_add_floor (x j)
  have hv := hp t ht y (fun j => ⌊x j⌋)
  rw [he] at hv
  change f (t,x) = f (t,y) at hv
  rw [hv]
  exact (hC (t,y) ⟨ht,hy⟩).trans (le_max_left _ _)

theorem planePeriodic_totalDerivative {f : ℝ × Plane → F}
    (hf : ContDiff ℝ ∞ f) (hp : ∀ t, PlanePeriodic (fun x => f (t,x))) (t : ℝ) :
    PlanePeriodic (fun x => fderiv ℝ f (t,x)) := by
  intro x k
  have hs : ∀ p : ℝ × Plane, f (p+(0,fun j => (k j : ℝ))) = f p := by
    rintro ⟨s,y⟩
    simpa only [Prod.mk_add_mk, add_zero] using hp s y k
  have h := fderiv_translation (hf.differentiable (by simp)) hs (t,x)
  simpa only [Prod.mk_add_mk, add_zero] using h

theorem timeSlice_hasDerivAt {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => f (s,x)) (fderiv ℝ f (t,x) (1,0)) t := by
  exact (hf.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

theorem timeSlice_norm_derivative_le {f : ℝ × Plane → F} {C t : ℝ} {x : Plane}
    (hC : ‖fderiv ℝ f (t,x)‖ ≤ C) : ‖fderiv ℝ f (t,x) (1,0)‖ ≤ C := by
  calc
    _ ≤ ‖fderiv ℝ f (t,x)‖ * ‖((1 : ℝ), (0 : Plane))‖ :=
      (fderiv ℝ f (t,x)).le_opNorm _
    _ = ‖fderiv ℝ f (t,x)‖ := by simp
    _ ≤ C := hC

theorem planePeriodic_time_lipschitz {f : ℝ × Plane → F}
    (hf : ContDiff ℝ ∞ f) (hp : ∀ t, PlanePeriodic (fun x => f (t,x))) (a b : ℝ) :
    ∃ L : ℝ≥0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x,
      ‖f (s,x)-f (t,x)‖ ≤ L * |s-t| := by
  obtain ⟨C,hC,hb⟩ := planePeriodic_bound_on
    (hf.continuous_fderiv (by simp)).continuousOn
    (fun t _ => planePeriodic_totalDerivative hf hp t) (a := a) (b := b)
  refine ⟨⟨C,hC⟩, ?_⟩
  intro s hs t ht x
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ Icc a b) => (timeSlice_hasDerivAt hf r x).hasDerivWithinAt)
    (fun r hr => timeSlice_norm_derivative_le (hb r hr x)) (convex_Icc a b) ht hs
  change ‖f (s,x)-f (t,x)‖ ≤ C * |s-t|
  simpa only [Real.norm_eq_abs] using h

omit [NormedSpace ℝ F] in
theorem supported_bound_on {f : ℝ × Plane → F} {a b : ℝ} {K : Set Plane}
    (hK : IsCompact K) (hf : ContinuousOn f (Icc a b ×ˢ K))
    (hs : ∀ t ∈ Icc a b, ∀ x ∉ K, f (t,x) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x, ‖f (t,x)‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hf
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · exact (hC (t,x) ⟨ht,hx⟩).trans (le_max_left _ _)
  · rw [hs t ht x hx, norm_zero]
    exact le_max_right _ _

theorem supported_time_lipschitz {f : ℝ × Plane → F}
    (hf : ContDiff ℝ ∞ f) {K : Set Plane} (hK : IsCompact K) (a b : ℝ)
    (hs : ∀ t ∈ Icc a b, ∀ x ∉ K, f (t,x) = 0) :
    ∃ L : ℝ≥0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x,
      ‖f (s,x)-f (t,x)‖ ≤ L * |s-t| := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by simp)).continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro s hs₀ t ht x
  by_cases hx : x ∈ K
  · have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r (_ : r ∈ Icc a b) => (timeSlice_hasDerivAt hf r x).hasDerivWithinAt)
      (fun r hr => timeSlice_norm_derivative_le
        ((hC (r,x) ⟨hr,hx⟩).trans (le_max_left C 0))) (convex_Icc a b) ht hs₀
    change ‖f (s,x)-f (t,x)‖ ≤ max C 0 * |s-t|
    simpa only [Real.norm_eq_abs] using h
  · rw [hs s hs₀ x hx, hs t ht x hx, sub_self, norm_zero]
    exact mul_nonneg (le_max_right _ _) (abs_nonneg _)

end ForcedComputation

end

end OAI
