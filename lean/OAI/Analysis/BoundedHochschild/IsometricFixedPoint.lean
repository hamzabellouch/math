import OAI.Analysis.BoundedHochschild.WeakIsometricFixedPoint
import Mathlib.GroupTheory.FreeGroup.Basic

namespace OAI

/-!
# Common fixed points for weakly compact linear isometric actions

A countable orbit generates a norm-separable closed convex hull. Applying
the separable argument to free groups on finitely many prescribed elements,
then using compactness, removes the separability restriction.
-/

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {G : Type v} [Group G]

/-- A countable acting group can be restricted to the separable closed
convex hull of one orbit. -/
theorem weakCompact_countable_isometric_fixedPoint [Countable G]
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ x ∈ C, ∀ g, weakIsometry (T g) x = x := by
  classical
  obtain ⟨x, hx⟩ := hne
  let S : Set E := Set.range (fun g : G => T g ((toWeakSpace ℂ E).symm x))
  let D : Set E := closure (convexHull ℝ S)
  let W : Set (WeakSpace ℂ E) := (toWeakSpace ℂ E) '' D
  have hDc : IsClosed D := isClosed_closure
  have hDv : Convex ℝ D := (convex_convexHull ℝ S).closure
  have hWc : IsClosed W := by
    rw [show W = closure ((toWeakSpace ℂ E) '' convexHull ℝ S) from
      (convex_convexHull ℝ S).toWeakSpace_closure ℂ]
    exact isClosed_closure
  have hWC : W ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    have hsub : D ⊆ (toWeakSpace ℂ E) ⁻¹' C := by
      apply closure_minimal _ (hC.isClosed.preimage (toWeakSpaceCLM ℂ E).continuous)
      apply convexHull_min _ (hconv.linear_preimage ((toWeakSpace ℂ E).restrictScalars ℝ).toLinearMap)
      rintro _ ⟨g, rfl⟩
      exact hinv g hx
    exact hsub hy
  have hWn : W.Nonempty := by
    refine ⟨x, (toWeakSpace ℂ E).symm x, ?_, (toWeakSpace ℂ E).apply_symm_apply x⟩
    apply subset_closure
    apply subset_convexHull ℝ S
    exact ⟨1, hone _⟩
  have hWs : IsSeparable ((toWeakSpace ℂ E).symm '' W) := by
    have hS : S.Countable := Set.countable_range _
    have hDsep : IsSeparable D := by
      apply (hS.isSeparable.span (R := ℝ)).closure.mono
      exact closure_mono (convexHull_min (Submodule.subset_span) (Submodule.span ℝ S).convex)
    have heq : (toWeakSpace ℂ E).symm '' W = D := by
      simp only [W, Set.image_image, LinearEquiv.symm_apply_apply, Set.image_id']
    rw [heq]
    exact hDsep
  have hWi : ∀ g, Set.MapsTo (weakIsometry (T g)) W W := by
    intro g a ha
    obtain ⟨y, hy, rfl⟩ := ha
    refine ⟨T g y, ?_, rfl⟩
    have hsub : D ⊆ (T g) ⁻¹' D := by
      apply closure_minimal _ (hDc.preimage (T g).continuous)
      apply convexHull_min _ (hDv.linear_preimage ((T g).toLinearMap.restrictScalars ℝ))
      rintro _ ⟨h, rfl⟩
      apply subset_closure
      apply subset_convexHull ℝ S
      exact ⟨g * h, hmul g h _⟩
    exact hsub hy
  obtain ⟨y, hy, hfix⟩ := weakCompact_separable_isometric_fixedPoint T hone hmul W
    (hC.of_isClosed_subset hWc hWC) hWn
    (hDv.linear_image ((toWeakSpace ℂ E).restrictScalars ℝ).toLinearMap) hWs hWi
  exact ⟨y, hWC hy, hfix⟩

/-- The linear-isometric case of the Ryll-Nardzewski fixed-point theorem,
without separability assumptions. -/
theorem weakCompact_isometric_fixedPoint
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (C : Set (WeakSpace ℂ E)) (hC : IsCompact C) (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) C C) :
    ∃ x ∈ C, ∀ g, weakIsometry (T g) x = x := by
  classical
  have hfinite (s : Finset G) : ∃ x ∈ C, ∀ g ∈ s, weakIsometry (T g) x = x := by
    let ρ : FreeGroup s →* G := FreeGroup.lift (fun g : s => g.val)
    have : Countable (FreeGroup s) := inferInstanceAs (Countable (Quot _))
    obtain ⟨x, hx, hfix⟩ := weakCompact_countable_isometric_fixedPoint (fun g => T (ρ g))
      (fun x => by simpa only [map_one] using hone x)
      (fun g h x => by simpa only [map_mul] using hmul (ρ g) (ρ h) x)
      C hC hne hconv (fun g => hinv (ρ g))
    refine ⟨x, hx, fun g hg => ?_⟩
    simpa only [ρ, FreeGroup.lift_apply_of] using hfix (FreeGroup.of ⟨g, hg⟩)
  let F (g : G) : Set (WeakSpace ℂ E) := {x | weakIsometry (T g) x = x}
  have hc (g) : IsClosed (F g) := isClosed_eq
    (WeakSpace.map (T g).toContinuousLinearEquiv.toContinuousLinearMap).continuous continuous_id
  obtain ⟨x, hx, hfix⟩ := hC.inter_iInter_nonempty F hc (fun s => by
    obtain ⟨x, hx, hfix⟩ := hfinite s
    exact ⟨x, hx, Set.mem_iInter₂.mpr hfix⟩)
  exact ⟨x, hx, fun g => Set.mem_iInter.mp hfix g⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
