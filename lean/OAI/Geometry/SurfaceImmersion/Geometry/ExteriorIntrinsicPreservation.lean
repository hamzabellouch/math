import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorBoundaryPreservation
import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorClosureControl
import OAI.Geometry.SurfaceImmersion.Primitive.IntrinsicExteriorCrossings
import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryJetCrossings

namespace OAI

/-! The actual exterior comparison retained by a primitive step preserves
all strict boundary data on compact curve portions and crossing sets. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame GeometryPreservation VelocityFrame
variable {M X : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [TopologicalSpace X] [CompactSpace X]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem compact_exterior_intrinsic_crossing_preservation {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) {p : X → M} (hp : Continuous p) (hpi : ∀ x, p x ∈ tsupport (A.weight i))
    {v w : X → SmallModes.Base} (hv : Continuous v) (hw : Continuous w)
    (hpositive : ∀ x,
      0 < realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i F) (v x) (v x)
        (planeCoordinateIsometry (chart (i : M) (p x))) ⬝ᵥ spaceCoordinates (n.vector (p x)) ∧
      0 < realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i F) (w x) (w x)
        (planeCoordinateIsometry (chart (i : M) (p x))) ⬝ᵥ spaceCoordinates (n.vector (p x)))
    (hcross : ∀ x,
      0 < orderedCrossing (spaceCoordinates ∘ A.vectorPlaneRead i F) (v x) (w x)
        (planeCoordinateIsometry (chart (i : M) (p x))) (coordinateGaussianCurvature (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i F) dx dx)
        (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i F) dx dy)
        (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i F) dy dy)
        (planeCoordinateIsometry (chart (i : M) (p x)))) ∧
      0 < orderedCrossing (spaceCoordinates ∘ A.vectorPlaneRead i F) (w x) (v x)
        (planeCoordinateIsometry (chart (i : M) (p x))) (coordinateGaussianCurvature (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i F) dx dx)
        (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i F) dx dy)
        (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i F) dy dy)
        (planeCoordinateIsometry (chart (i : M) (p x))))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ q ∈ O, V =ᶠ[𝓝 q] G) →
      ∀ x : X, p x ∈ closure O →
      (0 < realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i W) (v x) (v x)
        (planeCoordinateIsometry (chart (i : M) (p x))) ⬝ᵥ
          spaceCoordinates (A.unitProjectedNormalField W n.vector (p x)) ∧
       0 < realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i W) (w x) (w x)
        (planeCoordinateIsometry (chart (i : M) (p x))) ⬝ᵥ
          spaceCoordinates (A.unitProjectedNormalField W n.vector (p x))) ∧
      (0 < orderedCrossing (spaceCoordinates ∘ A.vectorPlaneRead i W) (v x) (w x)
        (planeCoordinateIsometry (chart (i : M) (p x))) (coordinateGaussianCurvature (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i W) dx dx)
        (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i W) dx dy)
        (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i W) dy dy)
        (planeCoordinateIsometry (chart (i : M) (p x)))) ∧
       0 < orderedCrossing (spaceCoordinates ∘ A.vectorPlaneRead i W) (w x) (v x)
        (planeCoordinateIsometry (chart (i : M) (p x))) (coordinateGaussianCurvature (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i W) dx dx)
        (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i W) dx dy)
        (realMetric (spaceCoordinates ∘ A.vectorPlaneRead i W) dy dy)
        (planeCoordinateIsometry (chart (i : M) (p x))))) := by
  have hread := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)
  have hcoord := A.continuous_planeChart_on_weight i hp hpi
  have hn := spaceCoordinates.continuous.comp (n.smooth.continuous.comp hp)
  have hD := fun x => A.planeRead_gram_of_immersion hF hI houter i (hpi x)
  obtain ⟨δv,hδv,hvclose⟩ := compact_actual_exterior_pairing hread hcoord hn hv hD
    (fun x => (hpositive x).1)
  obtain ⟨δw,hδw,hwclose⟩ := compact_actual_exterior_pairing hread hcoord hn hw hD
    (fun x => (hpositive x).2)
  have hB (a : X → SmallModes.Base) (h : ∀ x, 0 < realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (a x) (a x) (planeCoordinateIsometry (chart (i : M) (p x))) ⬝ᵥ spaceCoordinates (n.vector (p x))) :
      ∀ x, realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i F) (a x) (a x)
        (planeCoordinateIsometry (chart (i : M) (p x))) ≠ 0 := by
    intro x he
    have hx := h x
    rw [he,zero_dotProduct] at hx
    exact lt_irrefl 0 hx
  obtain ⟨δc,hδc,hcclose⟩ := compact_actual_intrinsic_crossings hread hcoord hv hw hD
    (hB v (fun x => (hpositive x).1)) (hB w (fun x => (hpositive x).2)) hcross
  let δ := min δv (min δw δc)
  have hδ : 0 < δ := lt_min hδv (lt_min hδw hδc)
  have hδv' : δ ≤ δv := min_le_left _ _
  have hδw' : δ ≤ δw := (min_le_right _ _).trans (min_le_left _ _)
  have hδc' : δ ≤ δc := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ρ,hρ,hcontrol⟩ := A.exterior_jet_normal_control_closure hF hI n houter hδ
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV O hext x hxO
  obtain ⟨hjet,_,hnorm⟩ := hcontrol G V W hG hV hW b c hb hc hbc hGF hWV O hext i (p x) hxO (hpi x)
  have hW' := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hW)
  exact ⟨⟨hvclose x _ hW' _ (hjet.trans_le hδv') (hnorm.trans_le hδv'),
    hwclose x _ hW' _ (hjet.trans_le hδw') (hnorm.trans_le hδw')⟩,
    hcclose x _ hW' (hjet.trans_le hδc')⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
