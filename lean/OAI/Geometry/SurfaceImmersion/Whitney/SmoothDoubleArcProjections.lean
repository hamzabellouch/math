import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleArc
import OAI.Geometry.SurfaceImmersion.Whitney.DoubleCurveVelocities

namespace OAI

/-! Both sheets and their common image are regular along a smooth double
arc whenever the two surface points are regular. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3}
namespace SmoothDoubleArc

theorem regular_projections (P : SmoothDoubleArc f)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) {t : ℝ}
    (ht : t ∈ P.arc.domain)
    (hAf : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P.arc.curve t).1))
    (hBf : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P.arc.curve t).2)) :
    Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun u => (P.arc.curve u).1) t) ∧
    Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun u => (P.arc.curve u).2) t) ∧
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,ProjectionTarget 3) (fun u => f (P.arc.curve u).1) t) := by
  have hP := P.arc.smooth.contMDiffAt (P.arc.domain_open.mem_nhds ht)
  have hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun u => (P.arc.curve u).1) t :=
    contMDiffAt_fst.comp t hP
  have hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun u => (P.arc.curve u).2) t :=
    contMDiffAt_snd.comp t hP
  have hpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun u => (P.arc.curve u).1) t).prod
        (mfderiv 𝓘(ℝ) planeModel (fun u => (P.arc.curve u).2) t)) := by
    have he := mfderiv_prodMk (hA.mdifferentiableAt (by simp)) (hB.mdifferentiableAt (by simp))
    exact he ▸ P.arc.regular t ht
  have heq : (fun u => f (P.arc.curve u).1) =ᶠ[𝓝 t] (fun u => f (P.arc.curve u).2) := by
    apply Filter.Eventually.of_forall
    intro u
    dsimp only
    rw [P.curve_eq]
    exact (P.lift u).property.2
  obtain ⟨hAi,hBi⟩ := regular_double_curve_velocities hf hA hB heq hpair hAf hBf
  refine ⟨hAi,hBi,?_⟩
  change Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,ProjectionTarget 3)
    (f ∘ fun u => (P.arc.curve u).1) t)
  rw [mfderiv_comp t (hf.mdifferentiable (by simp)).mdifferentiableAt
    (hA.mdifferentiableAt (by simp))]
  exact hAf.comp hAi

end SmoothDoubleArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
