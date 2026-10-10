import OAI.Geometry.Immersion.ClosedSurface.LocalPhaseData
import OAI.Geometry.Immersion.ClosedSurface.ChartModel
import OAI.Geometry.Immersion.ClosedSurface.SquarePartition

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Bundle Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]



structure PhasePatch (F : M → Space) (H : Base → PhaseMean.Tensor) (p : M) where
  G : RField 4
  ξ : Fin 3 → Base
  Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ
  O : Set Base
  V : Set M
  smooth : ContDiff ℝ ∞ G
  compact : HasCompactSupport G
  openO : IsOpen O
  centerO : coordinateCenter p ∈ O
  subdomain : O ⊆ coordinateDomain p
  agrees : EqOn G (coordinateMap F p) O
  openV : IsOpen V
  centerV : p ∈ V
  sourceV : V ⊆ (chartAt Plane p).source
  mapsV : ∀ q ∈ V, planeCoordinates (chartAt Plane p q) ∈ O
  decomposition : ∀ A, ∑ i, Q i A • covectorSquare (ξ i) = A
  admissible : ∀ x ∈ O, Function.Injective (fderiv ℝ (coordinateMap F p) x) ∧
    (∀ i, 0 < Q i (H x)) ∧ (∀ i, Good (realSecondTensor (coordinateMap F p) x) (ξ i)) ∧
    (∀ i j, i ≠ j → Good (realSecondTensor (coordinateMap F p) x) (ξ i + ξ j) ∧
      Good (realSecondTensor (coordinateMap F p) x) (ξ i - ξ j))



theorem exists_phasePatch {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (p : M) (hImm : Function.Injective (mfderiv planeModel spaceModel F p))
    (hB : ∃ v w : Base, realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0)
    {H : Base → PhaseMean.Tensor} (hH : ContinuousAt H (coordinateCenter p))
    (hH0 : 0 < H (coordinateCenter p) 0)
    (hHdet : 0 < H (coordinateCenter p) 0 * H (coordinateCenter p) 2 -
      (H (coordinateCenter p) 1)^2) : Nonempty (PhasePatch F H p) := by
  obtain ⟨G,ξ,Q,O,hG,hGc,hO,hpO,hsub,heq,hdec,ha⟩ := actual_local_phase_data_on
    (coordinateDomain_open p) (coordinateMap_smoothOn hF p) (coordinateCenter_mem p)
    hH (coordinateMap_immersion_center hF p hImm) hB hH0 hHdet
  let V : Set M := (chartAt Plane p).source ∩
    (chartAt Plane p) ⁻¹' (planeCoordinates ⁻¹' O)
  refine ⟨⟨G,ξ,Q,O,V,hG,hGc,hO,hpO,hsub,heq,?_,?_,?_,?_,hdec,ha⟩⟩
  · exact (chartAt Plane p).isOpen_inter_preimage (hO.preimage planeCoordinates.continuous)
  · refine ⟨mem_chart_source Plane p, ?_⟩
    simpa [coordinateCenter, planeModel] using hpO
  · exact fun q hq => hq.1
  · exact fun q hq => hq.2

variable [T2Space M] [CompactSpace M]



theorem exists_finite_phase_patches {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (hB : ∀ p, ∃ v w : Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0)
    (H : M → Base → PhaseMean.Tensor)
    (hH : ∀ p, ContinuousAt (H p) (coordinateCenter p))
    (hH0 : ∀ p, 0 < H p (coordinateCenter p) 0)
    (hHdet : ∀ p, 0 < H p (coordinateCenter p) 0 * H p (coordinateCenter p) 2 -
      (H p (coordinateCenter p) 1)^2) :
    ∃ (P : ∀ p, PhasePatch F (H p) p) (t : Finset M) (ψ : t → M → ℝ),
      (∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ (P i).V) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ i p, 0 ≤ ψ i p) ∧ (∀ p, ∑ i, (ψ i p)^2 = 1) := by
  classical
  let P : ∀ p, PhasePatch F (H p) p := fun p =>
    Classical.choice (exists_phasePatch hF p (hImm p) (hB p) (hH p) (hH0 p) (hHdet p))
  obtain ⟨t,ψ,hψ⟩ := exists_finite_smooth_square_partition (E := Plane)
    (fun p => (P p).V) (fun p => (P p).openV) (fun p => (P p).centerV)
  exact ⟨P,t,ψ,hψ⟩

end ClosedSurfaceR4

end

end OAI
