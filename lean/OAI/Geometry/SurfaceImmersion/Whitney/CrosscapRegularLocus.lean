import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTransverseDerivative

namespace OAI

/-! A genuine crosscap chart contains exactly one nonimmersed point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {f : M → ProjectionTarget 3} {p : M}

lemma SurfaceCrosscapCoordinates.regular_iff (c : SurfaceCrosscapCoordinates f p)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {x : M} (hx : x ∈ c.source.source) :
    Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) ↔ x ≠ p := by
  have hEq : EqOn (c.target ∘ standardCrosscap) (f ∘ c.source.symm) c.source.target := by
    intro y hy
    have hm := c.model_eq (c.source.symm y) (c.source.map_target hy)
    rw [c.source.right_inv hy] at hm
    exact hm.symm
  have hbridge := coordinate_representative_immersion_iff c.source c.source_smooth
    c.source_inverse_smooth hf c.source.open_target (subset_refl _) hEq (c.source.map_source hx)
  rw [c.source.left_inv hx] at hbridge
  rw [← hbridge]
  have htD : c.target.MDifferentiable 𝓘(ℝ,Base × ℝ) 𝓘(ℝ,ProjectionTarget 3) :=
    ⟨c.target_smooth.contMDiff.contMDiffOn.mdifferentiableOn (by simp),
      c.target_inverse_smooth.contMDiffOn.mdifferentiableOn (by simp)⟩
  have htI : Function.Injective (fderiv ℝ c.target (standardCrosscap (c.source x))) := by
    rw [← mfderiv_eq_fderiv]
    exact htD.mfderiv_injective (c.model_mem x hx)
  rw [fderiv_comp (c.source x) (c.target_smooth.differentiable (by simp) _)
    (standardCrosscap_hasFDerivAt _).differentiableAt]
  have hcomp : Function.Injective ((fderiv ℝ c.target (standardCrosscap (c.source x))).comp
      (fderiv ℝ standardCrosscap (c.source x))) ↔
      Function.Injective (fderiv ℝ standardCrosscap (c.source x)) := by
    constructor
    · intro h u v huv
      exact h (congrArg (fderiv ℝ c.target (standardCrosscap (c.source x))) huv)
    · intro h
      exact htI.comp h
  rw [hcomp,standardCrosscap_immersion_iff]
  constructor
  · intro hn he
    apply hn
    rw [he,c.source_center]
  · intro hn hz
    apply hn
    exact c.source.injOn hx c.source_mem (hz.trans c.source_center.symm)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
