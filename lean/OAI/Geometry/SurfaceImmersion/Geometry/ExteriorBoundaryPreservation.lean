import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorJetNormalControl
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

omit [CompactSpace M] [CompactSpace X] in
lemma continuous_planeChart_on_weight (i : A.centers) {p : X → M} (hp : Continuous p)
    (hpi : ∀ x, p x ∈ tsupport (A.weight i)) :
    Continuous (fun x => planeCoordinateIsometry (chart (i : M) (p x))) :=
  planeCoordinateIsometry.continuous.comp
    ((chart (i : M)).continuousOn.comp_continuous hp (fun x => A.weight_support i (hpi x)))

theorem compact_exterior_curve_preservation {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) {p : X → M} (hp : Continuous p) (hpi : ∀ x, p x ∈ tsupport (A.weight i))
    {v : X → SmallModes.Base} (hv : Continuous v)
    (hB : ∀ x, realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i F) (v x) (v x)
      (planeCoordinateIsometry (chart (i : M) (p x))) ≠ 0)
    (havoid : ∀ x, spaceCoordinates (n.vector (p x)) ≠
      -normalize (realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i F) (v x) (v x)
        (planeCoordinateIsometry (chart (i : M) (p x))))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ x : X, V =ᶠ[𝓝 (p x)] G →
      realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i W) (v x) (v x)
        (planeCoordinateIsometry (chart (i : M) (p x))) ≠ 0 ∧
      spaceCoordinates (A.unitProjectedNormalField W n.vector (p x)) ≠
        -normalize (realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i W) (v x) (v x)
          (planeCoordinateIsometry (chart (i : M) (p x)))) := by
  have hread := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)
  obtain ⟨δ,hδ,hclose⟩ := compact_actual_exterior_avoidance hread
    (A.continuous_planeChart_on_weight i hp hpi)
    (spaceCoordinates.continuous.comp (n.smooth.continuous.comp hp)) hv
    (fun x => A.planeRead_gram_of_immersion hF hI houter i (hpi x)) hB havoid
  obtain ⟨ρ,hρ,hcontrol⟩ := A.exterior_jet_normal_control hF hI n houter hδ
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV x he
  obtain ⟨hjet,_,hnorm⟩ := hcontrol G V W hG hV hW b c hb hc hbc hGF hWV i (p x) (hpi x) he
  exact hclose x _ (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hW)) _ hjet hnorm

theorem compact_exterior_crossing_preservation {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) {p : X → M} (hp : Continuous p) (hpi : ∀ x, p x ∈ tsupport (A.weight i))
    {v w : X → SmallModes.Base} {κ : X → ℝ} (hv : Continuous v) (hw : Continuous w) (hκ : Continuous κ)
    (hpositive : ∀ x,
      0 < realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i F) (v x) (v x)
        (planeCoordinateIsometry (chart (i : M) (p x))) ⬝ᵥ spaceCoordinates (n.vector (p x)) ∧
      0 < realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i F) (w x) (w x)
        (planeCoordinateIsometry (chart (i : M) (p x))) ⬝ᵥ spaceCoordinates (n.vector (p x)))
    (hcross : ∀ x,
      0 < orderedCrossing (spaceCoordinates ∘ A.vectorPlaneRead i F) (v x) (w x)
        (planeCoordinateIsometry (chart (i : M) (p x))) (κ x) ∧
      0 < orderedCrossing (spaceCoordinates ∘ A.vectorPlaneRead i F) (w x) (v x)
        (planeCoordinateIsometry (chart (i : M) (p x))) (κ x)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ x : X, V =ᶠ[𝓝 (p x)] G →
      (0 < realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i W) (v x) (v x)
        (planeCoordinateIsometry (chart (i : M) (p x))) ⬝ᵥ
          spaceCoordinates (A.unitProjectedNormalField W n.vector (p x)) ∧
       0 < realSecondForm (spaceCoordinates ∘ A.vectorPlaneRead i W) (w x) (w x)
        (planeCoordinateIsometry (chart (i : M) (p x))) ⬝ᵥ
          spaceCoordinates (A.unitProjectedNormalField W n.vector (p x))) ∧
      (0 < orderedCrossing (spaceCoordinates ∘ A.vectorPlaneRead i W) (v x) (w x)
        (planeCoordinateIsometry (chart (i : M) (p x))) (κ x) ∧
       0 < orderedCrossing (spaceCoordinates ∘ A.vectorPlaneRead i W) (w x) (v x)
        (planeCoordinateIsometry (chart (i : M) (p x))) (κ x)) := by
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
  obtain ⟨δc,hδc,hcclose⟩ := compact_actual_exterior_crossings hread hcoord hv hw hκ hD
    (hB v (fun x => (hpositive x).1)) (hB w (fun x => (hpositive x).2)) hcross
  let δ := min δv (min δw δc)
  have hδ : 0 < δ := lt_min hδv (lt_min hδw hδc)
  have hδv' : δ ≤ δv := min_le_left _ _
  have hδw' : δ ≤ δw := (min_le_right _ _).trans (min_le_left _ _)
  have hδc' : δ ≤ δc := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ρ,hρ,hcontrol⟩ := A.exterior_jet_normal_control hF hI n houter hδ
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV x he
  obtain ⟨hjet,_,hnorm⟩ := hcontrol G V W hG hV hW b c hb hc hbc hGF hWV i (p x) (hpi x) he
  have hW' := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hW)
  exact ⟨⟨hvclose x _ hW' _ (hjet.trans_le hδv') (hnorm.trans_le hδv'),
    hwclose x _ hW' _ (hjet.trans_le hδw') (hnorm.trans_le hδw')⟩,
    hcclose x _ hW' (hjet.trans_le hδc')⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
