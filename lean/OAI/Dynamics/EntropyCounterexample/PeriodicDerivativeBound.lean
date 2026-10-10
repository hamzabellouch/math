import Mathlib

namespace OAI

noncomputable section
namespace Problem340

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_add_eq_of_equivariant {a : E} {b : F} {H : E → F}
    (hH : ∀ x, H (x + a) = H x + b) (x : E) :
    fderiv ℝ H (x + a) = fderiv ℝ H x := by
  calc
    _ = fderiv ℝ (fun y => H (y + a)) x := (fderiv_comp_add_right a).symm
    _ = fderiv ℝ (fun y => H y + b) x := congrArg (fun f => fderiv ℝ f x) (funext hH)
    _ = fderiv ℝ H x := fderiv_add_const b

theorem exists_uniform_bound_of_periodic_cylinder
    {Z F : Type*} [TopologicalSpace Z] [NormedAddCommGroup F]
    {K : Set Z} {H : ℝ × Z → F} {p : ℝ}
    (hK : IsCompact K) (hp : 0 < p)
    (hH : ContinuousOn H (Set.Icc 0 p ×ˢ K))
    (hperiod : ∀ z ∈ K, Function.Periodic (fun t => H (t, z)) p) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t z, z ∈ K → ‖H (t, z)‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hH
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro t z hz
  obtain ⟨r, hr, heq⟩ := (hperiod z hz).exists_mem_Ico₀ hp t
  rw [heq]
  exact (hC (r, z) ⟨⟨hr.1, hr.2.le⟩, hz⟩).trans (le_max_right _ _)

theorem exists_uniform_fderiv_bound_of_equivariant
    {K : Set E} {G : ℝ × E → F} {p : ℝ} {b : F}
    (hK : IsCompact K) (hp : 0 < p) (hG : ContDiff ℝ 1 G)
    (hequiv : ∀ x, G (x + (p, 0)) = G x + b) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t z, z ∈ K → ‖fderiv ℝ G (t, z)‖ ≤ B := by
  have hperiod : ∀ z ∈ K,
      Function.Periodic (fun t => fderiv ℝ G (t, z)) p := by
    intro z _ t
    simpa using fderiv_add_eq_of_equivariant hequiv (t, z)
  exact exists_uniform_bound_of_periodic_cylinder hK hp
    (hG.continuous_fderiv one_ne_zero).continuousOn hperiod

end Problem340

end

end OAI
