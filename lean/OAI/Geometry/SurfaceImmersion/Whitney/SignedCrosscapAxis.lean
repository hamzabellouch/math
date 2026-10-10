import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisCurve

namespace OAI

/-! Signed kernel-axis curves are smooth, regular and injective throughout
the actual domain of the crosscap source chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

theorem signed_axis_curve (c : SurfaceCrosscapCoordinates f p) {s : ℝ} (hs : s ≠ 0) :
    ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => c.axisCurve (s*t))
      {t | crosscapAxis (s*t) ∈ c.source.target} ∧
    (∀ t, crosscapAxis (s*t) ∈ c.source.target →
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => c.axisCurve (s*t)) t)) ∧
    ({t | crosscapAxis (s*t) ∈ c.source.target}).InjOn (fun t => c.axisCurve (s*t)) := by
  let L : ℝ →L[ℝ] Base := crosscapAxis.comp (s • ContinuousLinearMap.id ℝ ℝ)
  have hL : ∀ t, L t = crosscapAxis (s*t) := fun _ => rfl
  have hLi : Function.Injective L := by
    intro x y he
    exact mul_left_cancel₀ hs (crosscapAxis_injective he)
  have hLs : ContMDiff 𝓘(ℝ) 𝓘(ℝ,Base) ∞ L := L.contDiff.contMDiff
  have hLd (t : ℝ) : Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) L t) := by
    have hd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ,Base) L t L := L.hasFDerivAt.hasMFDerivAt
    exact hd.mfderiv.symm ▸ hLi
  have hdif : c.source.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨c.source_inverse_smooth.mdifferentiableOn (by simp),c.source_smooth.mdifferentiableOn (by simp)⟩
  refine ⟨?_,?_,?_⟩
  · change ContMDiffOn 𝓘(ℝ) planeModel ∞ (c.source.symm ∘ L) (L ⁻¹' c.source.target)
    exact c.source_inverse_smooth.comp hLs.contMDiffOn (fun _ ht => ht)
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ) planeModel (c.source.symm ∘ L) t)
    rw [mfderiv_comp t
      ((c.source_inverse_smooth.contMDiffAt (c.source.open_target.mem_nhds ht)).mdifferentiableAt (by simp))
      (hLs.mdifferentiable (by simp) t)]
    exact (hdif.mfderiv_injective ht).comp (hLd t)
  · intro x hx y hy he
    apply hLi
    exact c.source.symm.injOn hx hy he

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
