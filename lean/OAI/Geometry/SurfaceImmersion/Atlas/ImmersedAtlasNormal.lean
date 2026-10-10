import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorProjectedNormal
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasImmersionGeometry

namespace OAI

/-! Discharge the projection's Gram hypotheses from the actual immersion. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma planeRead_gram_of_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) {p : M} (hp : p ∈ tsupport (A.weight i)) :
    gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p)))
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p))) ≠ 0 := by
  have he := A.vectorPlaneRead_eventually_coordinateMap F i (houter i) hp
  change gramDet (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) _ dx)
    (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) _ dy) ≠ 0
  rw [he.fderiv_eq]
  apply gramDet_ne_zero_of_injective
  apply coordinateMap_injective_of_immersion hF hI (i : M)
  change planeCoordinateIsometry (chart (i : M) p) ∈ (coordinateChart (i : M)).target
  rw [planeCoordinateIsometry_chart]
  exact (coordinateChart (i : M)).map_source (A.weight_support i hp)

lemma planeWeight_gram_of_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) {x : SmallModes.Base} (hx : x ∈ tsupport (A.planeWeight i)) :
    gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0 := by
  have hh := (A.supportedPlaneWeight i).tsupport_subset hx
  rcases hh with ⟨q,hq,rfl⟩
  rcases hq with ⟨p,hp,rfl⟩
  exact A.planeRead_gram_of_immersion hF hI houter i hp

theorem exterior_preferred_normal {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W →
      (∀ p, Function.Injective (surfaceDifferential W p)) →
      ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ U : Set M, (∀ p ∈ U, V =ᶠ[𝓝 p] G) →
      ContMDiffOn planeModel spaceModel ∞ (A.unitProjectedNormalField W n.vector) U ∧
      (∀ p ∈ U, ‖A.unitProjectedNormalField W n.vector p‖ = 1) ∧
      (∀ p ∈ U, ∀ v : TangentSpace planeModel p,
        inner ℝ (surfaceDifferential W p v) (A.unitProjectedNormalField W n.vector p) = 0) ∧
      (∀ p ∈ U, ‖A.unitProjectedNormalField W n.vector p-n.vector p‖ < ε) := by
  obtain ⟨ρ,hρ,hclose⟩ := A.exterior_projected_normal_close hF n.smooth n.unit n.normal
    (fun i p hp => A.planeRead_gram_of_immersion hF hI houter i hp) houter hε
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW hWI b c hb hc hbc hGF hWV U hext
  have hc := fun p hp => hclose G V W hG hV hW b c hb hc hbc hGF hWV p (hext p hp)
  obtain ⟨hs,hu,hn⟩ := A.unitProjectedNormalField_properties hW n.smooth
    (fun i x hx => A.planeWeight_gram_of_immersion hW hWI houter i hx) (fun p hp => (hc p hp).1)
  exact ⟨hs,hu,hn,fun p hp => (hc p hp).2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
