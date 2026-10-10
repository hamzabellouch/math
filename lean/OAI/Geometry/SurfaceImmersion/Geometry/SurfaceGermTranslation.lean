import OAI.Geometry.SurfaceImmersion.Geometry.FiniteGermSeparator

namespace OAI

/-! Smooth supported translation families and their unchanged first jets
at points where the scalar separator is locally constant. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def surfaceTranslation (f : M → ProjectionTarget 3) (χ : M → ℝ)
    (a : ProjectionTarget 3) : M → ProjectionTarget 3 := fun p => f p + χ p • a

omit [IsManifold planeModel ∞ M] in
theorem surfaceTranslation_smooth {f : M → ProjectionTarget 3} {χ : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ) (a : ProjectionTarget 3) :
    ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (surfaceTranslation f χ a) :=
  hf.add (hχ.smul contMDiff_const)

omit [ChartedSpace Plane M] [IsManifold planeModel ∞ M] in
theorem surfaceTranslation_germ {f : M → ProjectionTarget 3} {χ : M → ℝ}
    {p : M} {c : ℝ} (hχ : χ =ᶠ[𝓝 p] (fun _ => c)) (a : ProjectionTarget 3) :
    surfaceTranslation f χ a =ᶠ[𝓝 p] (fun q => f q+c • a) := by
  filter_upwards [hχ] with q hq
  simp only [surfaceTranslation,hq]

omit [IsManifold planeModel ∞ M] in
theorem surfaceTranslation_mfderiv {f : M → ProjectionTarget 3} {χ : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {p : M} {c : ℝ} (hχ : χ =ᶠ[𝓝 p] (fun _ => c)) (a : ProjectionTarget 3) :
    mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (surfaceTranslation f χ a) p =
      mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p := by
  rw [(surfaceTranslation_germ hχ a).mfderiv_eq]
  apply ContinuousLinearMap.ext
  intro v
  change (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (f + fun _ => c • a) p) v = _
  rw [mfderiv_add ((hf p).mdifferentiableAt (by simp)) mdifferentiableAt_const,
    mfderiv_const]
  change (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) v + 0 = _
  exact add_zero _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
