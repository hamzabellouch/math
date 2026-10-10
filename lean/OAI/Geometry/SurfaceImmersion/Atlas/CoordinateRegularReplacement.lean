import OAI.Geometry.SurfaceImmersion.Atlas.CoordinatePushforward
import OAI.Geometry.SurfaceImmersion.Whitney.SourceMapRepresentative

namespace OAI

/-! A supported coordinate replacement preserving differential rank
preserves the exact regular locus on the original surface. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [T2Space M]

theorem coordinate_regular_replacement (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {φ Q : Base → ProjectionTarget 3} (hQ : ContDiff ℝ ∞ Q)
    (hc : HasCompactSupport Q) {O : Set Base} (hO : IsOpen O) (hOt : O ⊆ c.target)
    (hs : tsupport Q ⊆ O) (hmatch : EqOn φ (f ∘ c.symm) O)
    (hrel : ∀ x ∈ tsupport Q, Function.Injective (fderiv ℝ (φ+Q) x) ↔
      Function.Injective (fderiv ℝ φ x)) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
      (∀ x ∉ c.symm '' tsupport Q, g =ᶠ[𝓝 x] f) ∧
      ∀ x ∈ c.source, c x ∈ O → g =ᶠ[𝓝 x] (φ+Q) ∘ c := by
  let g := f+coordinatePushforward c Q
  have hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g :=
    hf.add (coordinatePushforward_smooth c hcs hQ hc (hs.trans hOt))
  have hout : ∀ x ∉ c.symm '' tsupport Q, g =ᶠ[𝓝 x] f := by
    intro x hx
    have hn : x ∉ tsupport (coordinatePushforward c Q) :=
      fun h => hx (coordinatePushforward_tsupport c hc (hs.trans hOt) h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    change f y+coordinatePushforward c Q y = f y
    simp only [Pi.zero_apply] at hy
    rw [hy,add_zero]
  have hmatchG : EqOn (φ+Q) (g ∘ c.symm) O := by
    intro x hx
    have hxt := hOt hx
    change φ x+Q x = f (c.symm x)+coordinatePushforward c Q (c.symm x)
    rw [coordinatePushforward_source c Q (c.map_target hxt),c.right_inv hxt,hmatch hx]
    rfl
  refine ⟨g,hg,?_,hout,?_⟩
  · intro x
    by_cases hx : x ∈ c.symm '' tsupport Q
    · obtain ⟨z,hz,rfl⟩ := hx
      have hzO := hs hz
      have hiF := coordinate_representative_immersion_iff c hcs hci hf hO hOt hmatch hzO
      have hiG := coordinate_representative_immersion_iff c hcs hci hg hO hOt hmatchG hzO
      exact hiG.symm.trans ((hrel z hz).trans hiF)
    · rw [(hout x hx).mfderiv_eq]
      exact Iff.rfl
  · intro x hx hcx
    filter_upwards [c.open_source.mem_nhds hx,
      (c.continuousAt hx).preimage_mem_nhds (hO.mem_nhds hcx)] with y hy hyO
    have he := hmatchG hyO
    change (φ+Q) (c y) = g (c.symm (c y)) at he
    rw [c.left_inv hy] at he
    exact he.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
