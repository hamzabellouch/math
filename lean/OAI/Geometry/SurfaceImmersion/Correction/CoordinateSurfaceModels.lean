import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceCurveCoordinates

namespace OAI

/-! Smooth representatives and intrinsic transversality in constructed
surface coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem coordinate_representative (c : OpenPartialHomeomorph M Base)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {x : M} (hx : x ∈ c.source) :
    ∃ (V : Set Base) (F : Base → ProjectionTarget 3), IsOpen V ∧ c x ∈ V ∧
      V ⊆ c.target ∧ ContDiff ℝ ∞ F ∧ EqOn F (f ∘ c.symm) V := by
  have hlocal : ContDiffOn ℝ ∞ (f ∘ c.symm) c.target := (hf.comp_contMDiffOn hci).contDiffOn
  obtain ⟨V,hV,hxV,hVT,F,hF,hEq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := c x)) c.open_target (singleton_subset_iff.mpr (c.map_source hx)) hlocal
  exact ⟨V,F,hV,hxV (by simp),hVT,hF,hEq⟩

omit [ChartedSpace Plane M] in
lemma coordinate_representative_germ (c : OpenPartialHomeomorph M Base)
    {f : M → ProjectionTarget 3} {F : Base → ProjectionTarget 3} {x : M} (hx : x ∈ c.source)
    {V : Set Base} (hV : IsOpen V) (hxV : c x ∈ V) (hEq : EqOn F (f ∘ c.symm) V) :
    f =ᶠ[𝓝 x] F ∘ c := by
  filter_upwards [c.open_source.mem_nhds hx,(c.continuousAt hx).preimage_mem_nhds (hV.mem_nhds hxV)] with y hy hyV
  have he := hEq hyV
  change F (c y) = f (c.symm (c y)) at he
  rw [c.left_inv hy] at he
  exact he.symm

lemma coordinate_germ_mfderiv (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source) {x : M} (hx : x ∈ c.source)
    {f : M → ProjectionTarget 3} {F : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (he : f =ᶠ[𝓝 x] F ∘ c) :
    mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x =
      (fderiv ℝ F (c x)).comp (mfderiv planeModel 𝓘(ℝ,Base) c x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [he.mfderiv_eq,mfderiv_comp x
    (hF.contMDiff.mdifferentiable (by simp) (c x))
    ((hcs.contMDiffAt (c.open_source.mem_nhds hx)).mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
  rfl

theorem coordinate_pair_surjective (c d : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hds : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source)
    {x y : M} (hx : x ∈ c.source) (hy : y ∈ d.source)
    {f : M → ProjectionTarget 3} {F G : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (heF : f =ᶠ[𝓝 x] F ∘ c) (heG : f =ᶠ[𝓝 y] G ∘ d)
    (hreg : Function.Surjective (surfacePairDerivative f x y)) :
    Function.Surjective (fun z : Base × Base =>
      fderiv ℝ F (c x) z.1-fderiv ℝ G (d y) z.2) := by
  intro w
  obtain ⟨⟨u,v⟩,huv⟩ := hreg w
  refine ⟨(mfderiv planeModel 𝓘(ℝ,Base) c x u,mfderiv planeModel 𝓘(ℝ,Base) d y v),?_⟩
  simp only [surfacePairDerivative] at huv
  rw [coordinate_germ_mfderiv c hcs hx hF heF,coordinate_germ_mfderiv d hds hy hG heG] at huv
  exact huv

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
