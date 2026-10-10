import OAI.Geometry.SurfaceImmersion.Whitney.SupportedFormalImmersion
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateRegularReplacement

namespace OAI

/-! Relative local convex integration transferred through an actual surface chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [T2Space M]

/-- A constructed injective field removes precisely the singularities in the
chosen compact coordinate region; every exterior germ is preserved. -/
theorem surface_formal_immersion (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ)
    {O : Set Base} (hO : IsOpen O) (hOt : O ⊆ c.target)
    (hmatch : EqOn φ (f ∘ c.symm) O)
    {A : Base → Base →L[ℝ] ProjectionTarget 3} (hA : ContDiff ℝ ∞ A)
    {K₀ K₁ : Set Base} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (h01 : K₀ ⊆ interior K₁) (hK₁O : K₁ ⊆ O)
    (hs : tsupport (A-fderiv ℝ φ) ⊆ interior K₀)
    (hAI : ∀ x ∈ K₁, Function.Injective (A x)) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      (∀ x ∉ c.symm '' K₁, g =ᶠ[𝓝 x] f) ∧
      ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        x ∈ c.symm '' K₁ ∨
          Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) := by
  obtain ⟨F,hF,hsF,hFI,_hgC,_hreg⟩ :=
    HPrincipleBridge.supported_formal_immersion hφ hA hK₀ hK₁ h01 hs hAI
  let Q := F-φ
  have hQ : ContDiff ℝ ∞ Q := hF.sub hφ
  have hcQ : HasCompactSupport Q := hK₁.of_isClosed_subset (isClosed_tsupport Q) hsF
  have hsQ : tsupport Q ⊆ O := hsF.trans hK₁O
  let g := f+coordinatePushforward c Q
  have hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g :=
    hf.add (coordinatePushforward_smooth c hcs hQ hcQ (hsQ.trans hOt))
  have hout : ∀ x ∉ c.symm '' K₁, g =ᶠ[𝓝 x] f := by
    intro x hx
    have hn : x ∉ tsupport (coordinatePushforward c Q) := by
      intro hh
      obtain ⟨z,hz,he⟩ := coordinatePushforward_tsupport c hcQ (hsQ.trans hOt) hh
      exact hx ⟨z,hsF hz,he⟩
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    change f y+coordinatePushforward c Q y = f y
    simp only [Pi.zero_apply] at hy
    rw [hy,add_zero]
  have hmatchG : EqOn F (g ∘ c.symm) O := by
    intro x hx
    have hxt := hOt hx
    change F x = f (c.symm x)+coordinatePushforward c Q (c.symm x)
    rw [coordinatePushforward_source c Q (c.map_target hxt),c.right_inv hxt]
    have he := hmatch hx
    change φ x = f (c.symm x) at he
    change F x = f (c.symm x)+(F x-φ x)
    rw [←he]
    abel
  refine ⟨g,hg,hout,?_⟩
  intro x
  by_cases hx : x ∈ c.symm '' K₁
  · obtain ⟨z,hz,rfl⟩ := hx
    have hI := (coordinate_representative_immersion_iff c hcs hci hg hO hOt hmatchG
      (hK₁O hz)).mp (hFI z hz)
    exact iff_of_true hI (Or.inl ⟨z,hz,rfl⟩)
  · rw [(hout x hx).mfderiv_eq]
    exact (or_iff_right hx).symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
