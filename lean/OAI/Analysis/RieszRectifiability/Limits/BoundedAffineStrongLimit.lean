import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.BoundedBoxConvergence
import OAI.Analysis.RieszRectifiability.Limits.LipschitzRepresentativeStrongLimit
import OAI.Analysis.RieszRectifiability.Flatness.AmbientAffineHeight

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem bounded_height_strong_of_lipschitz_representative {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e)) (H : ℕ)
    (w : ℕ → Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (f v : Ambient d → ℝ) (J : ℝ≥0) (hv : LipschitzWith J v)
    (hfv : f =ᵐ[coordinatePlaneMeasure e] v)
    (hsecond : Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))
    (hmoment : ∀ (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x
        ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x * ψ x
          ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) :
    Tendsto (fun j => ∫ x, (w j x - v x) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop (𝓝 0) := by
  let μ := fun j => boundedProjectionFiniteMeasure (σ j) π (e 0) K H
  let ν := boxPlaneFiniteMeasure (exhaustionBox ι H) e
  have hνeq : (coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H) =
      (ν : Measure (Ambient d)) :=
    coordinatePlaneMeasure_restrict_boundedRegion e π K he hπ.continuous hleft H
  have hs := (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet
  have hμball : ∀ j, ∀ᵐ x ∂(μ j : Measure (Ambient d)),
      x ∈ ball (e 0) (planeBoxOuterRadius K H) := by
    intro j
    filter_upwards [ae_restrict_mem (μ := σ j) hs] with x hx
    exact hx.2
  have hνball : ∀ᵐ x ∂(ν : Measure (Ambient d)),
      x ∈ ball (e 0) (planeBoxOuterRadius K H) := by
    rw [← hνeq]
    filter_upwards [ae_restrict_mem (μ := coordinatePlaneMeasure e) hs] with x hx
    exact hx.2
  have hfv' : f =ᵐ[(ν : Measure (Ambient d))] v := by
    rw [← hνeq]
    exact ae_restrict_of_ae hfv
  apply strong_height_convergence_of_lipschitz_representative μ ν
    (boundedProjectionFiniteMeasure_tendsto e π K Q he hπ hleft σ hlocal H)
    (e 0) (planeBoxOuterRadius K H) hμball hνball w hw f v J hv hfv'
  · simpa only [hνeq] using! hsecond
  · intro ψ J B hc hLip hB
    simpa only [hνeq] using! hmoment ψ J B hc hLip hB

theorem bounded_height_strong_of_intrinsic_affine {n d : ℕ}
    (e : (Fin n → ℝ) → Ambient d) (π : Ambient d → Fin n → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient n →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e)) (H : ℕ)
    (w : ℕ → Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (f : Ambient d → ℝ) (hfm : Measurable f) (c : ℝ) (M : Ambient n →L[ℝ] ℝ)
    (hfa : ∀ᵐ x, f (a + L x) = c + M x)
    (hsecond : Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))
    (hmoment : ∀ (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x
        ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x * ψ x
          ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) :
    Tendsto (fun j => ∫ x, (w j x - ambientAffineHeight a L c M x) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop (𝓝 0) := by
  have hfv : f =ᵐ[coordinatePlaneMeasure e] ambientAffineHeight a L c M := by
    rw [hplane]
    exact height_ae_eq_ambient_affine a L f hfm c M hfa
  exact bounded_height_strong_of_lipschitz_representative e π K Q he hπ hleft σ hlocal H w hw
    f (ambientAffineHeight a L c M) _ (ambientAffineHeight_lipschitz a L c M) hfv hsecond hmoment

end

end RieszRectifiability

end OAI
