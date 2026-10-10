import OAI.Geometry.SurfaceImmersion.Geometry.FrozenTranslationGerms

namespace OAI

/-! Translation germs preserve the full first derivative, and hence
preserve the prepared singularities on the frozen neighborhoods. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma mfderiv_eq_of_translation_germ {f g : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {x : M} {a : ProjectionTarget 3} (he : g =ᶠ[𝓝 x] (fun y => f y+a)) :
    mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x =
      mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x := by
  rw [he.mfderiv_eq]
  apply ContinuousLinearMap.ext
  intro v
  change (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (f + fun _ => a) x) v = _
  rw [mfderiv_add ((hf x).mdifferentiableAt (by simp)) mdifferentiableAt_const,mfderiv_const]
  change (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) v+0 = _
  exact add_zero _

lemma FrozenTranslationGerms.mfderiv_eq {A : ι → Set M} {f g : M → ProjectionTarget 3}
    (h : FrozenTranslationGerms A f g)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (i : ι) {x : M} (hx : x ∈ A i) :
    mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x =
      mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x := by
  obtain ⟨a,ha⟩ := h i
  exact mfderiv_eq_of_translation_germ hf (ha.filter_mono (nhds_le_nhdsSet hx))

theorem frozen_immersion_equivalence {A : ι → Set M} {B : Set M}
    (hcover : B ∪ ⋃ i, A i = univ) {f g : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (h : FrozenTranslationGerms A f g)
    (hIf : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (hIg : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)) :
    ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) := by
  intro x
  have hx : x ∈ B ∪ ⋃ i, A i := by rw [hcover]; trivial
  rcases hx with hx | hx
  · exact iff_of_true (hIg x hx) (hIf x hx)
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    rw [h.mfderiv_eq hf i hi]
    exact Iff.rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
