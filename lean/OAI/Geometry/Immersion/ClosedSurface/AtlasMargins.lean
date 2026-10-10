import OAI.Geometry.Immersion.ClosedSurface.ChartTransition
import OAI.Geometry.Immersion.ClosedSurface.CoordinateMargins

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_transition (F : M → Space) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    coordinateMap F q (coordinateTransition q p x) = coordinateMap F p x := by
  change spaceCoordinates (F (coordinateInverse q (coordinateTransition q p x))) =
    spaceCoordinates (F (coordinateInverse p x))
  rw [← coordinateChart_symm_apply, ← coordinateChart_symm_apply]
  change spaceCoordinates (F ((coordinateChart q).symm
    (coordinateChart q ((coordinateChart p).symm x)))) = _
  have hqx : (coordinateChart p).symm x ∈ (coordinateChart q).source := hx.2
  rw [(coordinateChart q).left_inv hqx]

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_transition_eventuallyEq (F : M → Space) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    coordinateMap F q ∘ coordinateTransition q p =ᶠ[𝓝 x] coordinateMap F p := by
  filter_upwards [(coordinateTransition q p).open_source.mem_nhds hx] with y hy
  exact coordinateMap_transition F q p hy




theorem actual_chart_phase_margin {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) (ξ : SmallModes.Base)
    {d L ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateTransition q p x))
      (coordDeriv dy (coordinateMap F q) (coordinateTransition q p x)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) x)|)
    (hA : ‖fderiv ℝ (coordinateTransition q p) x‖ ≤ L)
    (hB : realSecondTensor (coordinateMap F q) (coordinateTransition q p x) ≠ 0)
    (hmargin : ε*‖realSecondTensor (coordinateMap F q) (coordinateTransition q p x)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F q) (coordinateTransition q p x)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ‖ ≤ 2*L*‖ξ‖ ∧
    d^2*ε/(4*L^2)*‖realSecondTensor (coordinateMap F p) x‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F p) x)
        (-(pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).2,
          (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).1)‖ ∧
    Good (realSecondTensor (coordinateMap F p) x)
      (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ) ∧
    realSecondTensor (coordinateMap F p) x ≠ 0 := by
  have hy : coordinateTransition q p x ∈ coordinateDomain q := by
    rw [← coordinateChart_target]
    exact (coordinateChart q).map_source hx.2
  have ht := quantitative_chart_phase_margin_on
    (coordinateTransition q p).open_source (coordinateDomain_open q)
    (coordinateMap_smoothOn hF q) (coordinateTransition_smoothOn q p)
    hx hy ξ hd hL hε hD hdet hA hB hmargin
  have he := (realSecondTensor_eventuallyEq
    (coordinateMap_transition_eventuallyEq F q p hx)).eq_of_nhds
  simpa only [he] using ht

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma coordinateChart_compact_image {K : Set M} (hK : IsCompact K) (p : M)
    (hKs : K ⊆ (coordinateChart p).source) :
    IsCompact (coordinateChart p '' K) := hK.image_of_continuousOn ((coordinateChart p).continuousOn.mono hKs)

omit [IsManifold planeModel ∞ M] in
lemma coordinateChart_image_overlap {K : Set M} (q p : M)
    (hKp : K ⊆ (coordinateChart p).source) (hKq : K ⊆ (coordinateChart q).source) :
    coordinateChart p '' K ⊆ (coordinateTransition q p).source := by
  rintro x ⟨a,ha,rfl⟩
  constructor
  · exact (coordinateChart p).map_source (hKp ha)
  · change (coordinateChart p).symm (coordinateChart p a) ∈ (coordinateChart q).source
    rw [(coordinateChart p).left_inv (hKp ha)]
    exact hKq ha




theorem compact_overlap_phase_margin {K : Set M} (hK : IsCompact K) (q p : M)
    (hKp : K ⊆ (coordinateChart p).source) (hKq : K ⊆ (coordinateChart q).source) :
    ∃ η L : ℝ, 0 < η ∧ 0 < L ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ x ∈ coordinateChart p '' K, ∀ ξ : SmallModes.Base, ∀ ε : ℝ, 0 < ε →
      NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateTransition q p x))
        (coordDeriv dy (coordinateMap F q) (coordinateTransition q p x)) ≠ 0 →
      realSecondTensor (coordinateMap F q) (coordinateTransition q p x) ≠ 0 →
      ε*‖realSecondTensor (coordinateMap F q) (coordinateTransition q p x)‖ ≤
        ‖secondQuadratic (realSecondTensor (coordinateMap F q) (coordinateTransition q p x)) (-ξ.2,ξ.1)‖ →
      ‖pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ‖ ≤ L*‖ξ‖ ∧
      η*ε*‖realSecondTensor (coordinateMap F p) x‖ ≤
        ‖secondQuadratic (realSecondTensor (coordinateMap F p) x)
          (-(pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).2,
            (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).1)‖ ∧
      Good (realSecondTensor (coordinateMap F p) x)
        (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ) ∧
      realSecondTensor (coordinateMap F p) x ≠ 0 := by
  obtain ⟨d,L,hd,hL,hbound⟩ := coordinateTransition_compact_bounds q p
    (coordinateChart_compact_image hK p hKp) (coordinateChart_image_overlap q p hKp hKq)
  refine ⟨d^2/(4*L^2),2*L,div_pos (sq_pos_of_pos hd)
    (mul_pos (by norm_num) (sq_pos_of_pos hL)),mul_pos (by norm_num) hL,?_⟩
  intro F hF x hx ξ ε hε hD hB hm
  have h := actual_chart_phase_margin hF q p
    (coordinateChart_image_overlap q p hKp hKq hx) ξ hd hL hε hD
    (hbound x hx).1 (hbound x hx).2 hB hm
  have he : d^2/(4*L^2)*ε = d^2*ε/(4*L^2) := by ring
  simpa only [he] using h

end ClosedSurfaceR4

end

end OAI
