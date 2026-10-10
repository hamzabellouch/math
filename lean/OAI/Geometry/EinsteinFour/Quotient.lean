import OAI.Geometry.Manifold.ProjectiveSphere

namespace OAI

/-!
# The metric quotient of the round four-sphere by a free involution

The orientation double cover in the manuscript's unoriented argument has a
free isometric deck involution. Once that cover is identified with the round
sphere, its metric quotient is the concrete real projective model below.
-/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff

/-- Identification of quotient fibers supplies an equivalence that sends the
quotient projection to the standard projectivization map. -/
theorem free_round_involution_quotient_equiv
    {M : Type*}
    (τ : RoundSphere4 → RoundSphere4)
    (hτ : Function.Involutive τ)
    (hτdistance : ∀ x y, roundDistance (τ x) (τ y) = roundDistance x y)
    (hτfree : ∀ x, τ x ≠ x)
    (p : RoundSphere4 → M) (hp : Function.Surjective p)
    (hfibers : ∀ x y, p x = p y ↔ x = y ∨ x = τ y) :
    ∃ e : M ≃ RealProjective4, ∀ x, e (p x) = sphereToProjective x := by
  classical
  have hprojective_fibers :=
    (free_round_involution_projective_fibers_and_distance τ hτ hτdistance hτfree).1
  have hsame : ∀ x y,
      p x = p y ↔ sphereToProjective x = sphereToProjective y := by
    intro x y
    exact (hfibers x y).trans (hprojective_fibers x y).symm
  let f : M → RealProjective4 := fun x => sphereToProjective (Function.surjInv hp x)
  have hf : ∀ x, f (p x) = sphereToProjective x := by
    intro x
    exact (hsame _ x).mp (Function.surjInv_eq hp (p x))
  have hf_injective : Function.Injective f := by
    intro x y hxy
    have hxy' : p (Function.surjInv hp x) = p (Function.surjInv hp y) :=
      (hsame _ _).mpr hxy
    simpa only [Function.surjInv_eq] using hxy'
  have hf_surjective : Function.Surjective f := by
    intro q
    obtain ⟨x, hx⟩ := sphereToProjective_surjective q
    exact ⟨p x, (hf x).trans hx⟩
  exact ⟨Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩, hf⟩

/-- A two-sheeted metric quotient of the round four-sphere by a free isometric
involution is equivalent to `RealProjective4`, with its stated model distance.
The quotient fibers and quotient-distance formula are explicit hypotheses; the
construction also identifies the quotient map with projectivization. -/
theorem free_round_involution_quotient_is_projective
    {M : Type*} (dM : M → M → ℝ)
    (τ : RoundSphere4 → RoundSphere4)
    (hτ : Function.Involutive τ)
    (hτdistance : ∀ x y, roundDistance (τ x) (τ y) = roundDistance x y)
    (hτfree : ∀ x, τ x ≠ x)
    (p : RoundSphere4 → M) (hp : Function.Surjective p)
    (hfibers : ∀ x y, p x = p y ↔ x = y ∨ x = τ y)
    (hdistance : ∀ x y,
      dM (p x) (p y) = min (roundDistance x y) (roundDistance x (τ y))) :
    ∃ e : M ≃ RealProjective4,
      (∀ x, e (p x) = sphereToProjective x) ∧
      ∀ x y, realProjectiveDistance (e x) (e y) = dM x y := by
  obtain ⟨e, he⟩ :=
    free_round_involution_quotient_equiv τ hτ hτdistance hτfree p hp hfibers
  have hprojective_distance :=
    (free_round_involution_projective_fibers_and_distance τ hτ hτdistance hτfree).2
  refine ⟨e, he, ?_⟩
  intro x y
  obtain ⟨x', rfl⟩ := hp x
  obtain ⟨y', rfl⟩ := hp y
  rw [he, he, hprojective_distance, hdistance]

/-- The quotient identification directly supplies the scaled metric conclusion
used by the classification statement. No sign assumption on `a` is needed for
this implication: the caller separately supplies positivity of the scale. -/
theorem scaled_round_involution_quotient_is_projective
    {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M]
    (g : SmoothMetric M) (a : ℝ)
    (τ : RoundSphere4 → RoundSphere4)
    (hτ : Function.Involutive τ)
    (hτdistance : ∀ x y, roundDistance (τ x) (τ y) = roundDistance x y)
    (hτfree : ∀ x, τ x ≠ x)
    (p : RoundSphere4 → M) (hp : Function.Surjective p)
    (hfibers : ∀ x y, p x = p y ↔ x = y ∨ x = τ y)
    (hdistance : ∀ x y, scaledEDistance g a (p x) (p y) =
      ENNReal.ofReal (min (roundDistance x y) (roundDistance x (τ y)))) :
    ScaledIsometricTo g a realProjectiveDistance := by
  obtain ⟨e, he⟩ :=
    free_round_involution_quotient_equiv τ hτ hτdistance hτfree p hp hfibers
  have hprojective_distance :=
    (free_round_involution_projective_fibers_and_distance τ hτ hτdistance hτfree).2
  refine ⟨e, ?_⟩
  intro x y
  obtain ⟨x', rfl⟩ := hp x
  obtain ⟨y', rfl⟩ := hp y
  rw [he, he, hprojective_distance, hdistance]

end PositiveEinsteinFour

end OAI
