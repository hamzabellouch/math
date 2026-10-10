import OAI.Geometry.SurfaceImmersion.Whitney.LocalDoubleCurveLift
import OAI.Geometry.SurfaceImmersion.Whitney.DoubleCurveParameter

namespace OAI

/-! A smooth regular pair curve locally contained in the double locus
has the actual chart parameter, with nonzero derivative. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem pair_curve_parameter (c : SmoothDoubleChart f) {C : ℝ → M × M} {x : ℝ}
    (p : surfaceDoublePairs f) (hp : p.val = C x) (hpc : p ∈ c.coord.source)
    (hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (C t).1) x)
    (hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (C t).2) x)
    (hpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (C t).1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (C t).2) x)))
    (hgood : ∀ᶠ t in 𝓝 x, C t ∈ surfaceDoublePairs f) :
    ∃ h : ℝ → ℝ, ContDiffAt ℝ ∞ h x ∧ deriv h x ≠ 0 ∧
      h x = c.coord p ∧ C =ᶠ[𝓝 x] (fun t => (c.coord.symm (h t)).val) := by
  have hC : ContinuousAt C x := hA.continuousAt.prodMk hB.continuousAt
  obtain ⟨γ,hγ,hγx,he⟩ := local_double_curve_lift hC p hp hgood
  have heA : (fun t => (γ t).val.1) =ᶠ[𝓝 x] (fun t => (C t).1) :=
    he.mono fun _ ht => congrArg Prod.fst ht
  have heB : (fun t => (γ t).val.2) =ᶠ[𝓝 x] (fun t => (C t).2) :=
    he.mono fun _ ht => congrArg Prod.snd ht
  have hγA := hA.congr_of_eventuallyEq heA
  have hγB := hB.congr_of_eventuallyEq heB
  have hDA := ((hA.mdifferentiableAt (by simp)).hasMFDerivAt.congr_of_eventuallyEq_abuse heA).mfderiv
  have hDB := ((hB.mdifferentiableAt (by simp)).hasMFDerivAt.congr_of_eventuallyEq_abuse heB).mfderiv
  have hγpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (γ t).val.2) x)) := by
    rw [hDA,hDB]
    exact hpair
  obtain ⟨h,hhs,hhn,hval,hinv⟩ := c.curve_parameter hγ (hγx ▸ hpc) hγA hγB hγpair
  refine ⟨h,hhs,hhn,by simpa only [hγx] using hval,?_⟩
  filter_upwards [he,hinv] with t ht ht'
  exact ht.symm.trans (congrArg Subtype.val ht')

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
