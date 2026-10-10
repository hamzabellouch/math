import FixedPointTheorems.brouwer

namespace OAI

/-!
# Filling an open neighborhood with physical parameters

The finite-dimensional step used in the proof of Theorem `thm:blowup`.
Brouwer's theorem gives a zero for a continuous perturbation of an invertible
linear parameter map when the boundary error is sufficiently small.
-/

open Metric Set

namespace DefocusingNLS

/-- A continuous perturbation of the identity on a ball covers the smaller ball. -/
theorem continuous_perturbation_covers_ball {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r δ : ℝ) (hr : 0 ≤ r)
    (f : closedBall (0 : E) r → E) (hf : Continuous f)
    (herror : ∀ x, ‖f x - x.val‖ ≤ δ) :
    closedBall (0 : E) (r - δ) ⊆ Set.range f := by
  intro z hz
  have hz' : ‖z‖ ≤ r - δ := by simpa using hz
  have hmaps (x : closedBall (0 : E) r) :
      z - (f x - x.val) ∈ closedBall (0 : E) r := by
    have hbound := (norm_sub_le z (f x - x.val)).trans (add_le_add hz' (herror x))
    simpa only [mem_closedBall, dist_zero_right, sub_add_cancel] using hbound
  let T : C(closedBall (0 : E) r, closedBall (0 : E) r) :=
    ⟨fun x => ⟨z - (f x - x.val), hmaps x⟩,
      (continuous_const.sub (hf.sub continuous_subtype_val)).subtype_mk _⟩
  obtain ⟨u, hu⟩ := brouwer_fixed_point (closedBall (0 : E) r)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
    ⟨0, mem_closedBall_self hr⟩ T
  have heq := congrArg (fun x : closedBall (0 : E) r => x.val) hu
  change z - (f u - u.val) = u.val at heq
  refine ⟨u, ?_⟩
  calc
    f u = (f u - u.val) + u.val := (sub_add_cancel _ _).symm
    _ = (f u - u.val) + (z - (f u - u.val)) := by rw [heq]
    _ = z := by abel

/-- The zero-existence specialization used after preconditioning by the
invertible physical-parameter matrix. -/
theorem zero_of_small_continuous_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r δ : ℝ) (hr : 0 ≤ r) (hδ : δ ≤ r)
    (f : closedBall (0 : E) r → E) (hf : Continuous f)
    (herror : ∀ x, ‖f x - x.val‖ ≤ δ) :
    ∃ x, f x = 0 := by
  apply continuous_perturbation_covers_ball r δ hr f hf herror
  simpa using (sub_nonneg.mpr hδ : 0 ≤ r - δ)

/-- The version applied to a map close to an invertible physical-parameter
matrix, after multiplication by its inverse. -/
theorem zero_of_near_invertible_linear_map {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : E ≃L[ℝ] E) (r δ : ℝ) (hr : 0 ≤ r) (hδ : δ ≤ r)
    (f : closedBall (0 : E) r → E) (hf : Continuous f)
    (herror : ∀ x, ‖C.symm (f x) - x.val‖ ≤ δ) :
    ∃ x, f x = 0 := by
  obtain ⟨x, hx⟩ := zero_of_small_continuous_error r δ hr hδ
    (fun x => C.symm (f x)) (C.symm.continuous.comp hf) herror
  refine ⟨x, ?_⟩
  simpa using congrArg C hx

/-- Phase, twelve translations, and logarithmic blowup time. -/
abbrev PhysicalParameters := ℝ × (Fin 12 → ℝ) × ℝ

/-- The leading parameter map in equation `nl:leading-expansion`. -/
def leadingParameterMap (b : ℝ) (d : PhysicalParameters) : PhysicalParameters :=
  (-d.1 + b * d.2.2, d.2.1, d.2.2)

/-- The leading matrix is its own inverse, for every phase frequency. -/
theorem leadingParameterMap_involutive (b : ℝ) :
    Function.Involutive (leadingParameterMap b) := by
  intro d
  rcases d with ⟨θ, ζ, β⟩
  simp only [leadingParameterMap, Prod.mk.injEq, and_true]
  ring

end DefocusingNLS

end OAI
