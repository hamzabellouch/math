import OAI.Geometry.SurfaceImmersion.Geometry.FrozenGermDerivative
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceRegularPairLocus

namespace OAI

/-! Translations on an entire frozen neighborhood preserve its internal
coincidences and their transverse tangent-plane geometry. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] [ChartedSpace Plane M] in
lemma FrozenTranslationGerms.coincidence_iff {A : ι → Set M} {f g : M → ProjectionTarget 3}
    (h : FrozenTranslationGerms A f g) (i : ι) {x y : M} (hx : x ∈ A i) (hy : y ∈ A i) :
    g x = g y ↔ f x = f y := by
  obtain ⟨a,ha⟩ := h i
  have hxg := (ha.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
  have hyg := (ha.filter_mono (nhds_le_nhdsSet hy)).self_of_nhds
  change g x = f x+a at hxg
  change g y = f y+a at hyg
  rw [hxg,hyg,add_left_inj]

omit [IsManifold planeModel ∞ M] in
lemma FrozenTranslationGerms.pairDerivative_eq {A : ι → Set M} {f g : M → ProjectionTarget 3}
    (h : FrozenTranslationGerms A f g)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (i : ι) {x y : M} (hx : x ∈ A i) (hy : y ∈ A i) :
    surfacePairDerivative g x y = surfacePairDerivative f x y := by
  unfold surfacePairDerivative
  rw [h.mfderiv_eq hf i hx,h.mfderiv_eq hf i hy]
  rfl

omit [IsManifold planeModel ∞ M] in
lemma FrozenTranslationGerms.regular_pair {A : ι → Set M} {f g : M → ProjectionTarget 3}
    (h : FrozenTranslationGerms A f g)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (i : ι) {x y : M} (hx : x ∈ A i) (hy : y ∈ A i)
    (hreg : (x,y) ∈ regularSurfacePairs f) : (x,y) ∈ regularSurfacePairs g := by
  rcases hreg with hreg | hreg
  · exact Or.inl fun hxy => hreg ((h.coincidence_iff i hx hy).mp hxy)
  · exact Or.inr (by rwa [h.pairDerivative_eq hf i hx hy])

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
