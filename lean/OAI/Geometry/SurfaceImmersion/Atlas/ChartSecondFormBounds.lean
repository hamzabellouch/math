import OAI.Geometry.Immersion.ClosedSurface.AtlasMargins
import OAI.Geometry.Immersion.ClosedSurface.AtlasPhases

namespace OAI

/-! Second-form norms in two fixed overlapping surface charts are comparable
with constants independent of the immersion. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

theorem norm_realSecondTensor_comp_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖realSecondTensor (F ∘ φ) p‖ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
  obtain ⟨G,hG,_,_,heG⟩ := smooth_extension_near hV hF.contMDiffOn hφp
  obtain ⟨Φ,hΦ,_,_,heΦ⟩ := smooth_extension_near hU hφ.contMDiffOn hp
  have ep := heΦ.eq_of_nhds
  have eD := heΦ.fderiv_eq (𝕜 := ℝ)
  have hc : ContinuousAt φ p := (hφ p hp).contDiffAt (hU.mem_nhds hp) |>.continuousAt
  have hecomp : G ∘ Φ =ᶠ[𝓝 p] F ∘ φ := by
    filter_upwards [heΦ,heG.comp_tendsto hc] with q hqΦ hqG
    simpa only [Function.comp_apply,hqΦ] using hqG
  have hDG : NormalFrame.gramDet (coordDeriv dx G (Φ p)) (coordDeriv dy G (Φ p)) ≠ 0 := by
    rw [ep,(coordDeriv_eventuallyEq heG dx).eq_of_nhds,
      (coordDeriv_eventuallyEq heG dy).eq_of_nhds]
    exact hD
  have hh := norm_realSecondTensor_comp_smooth hG.contDiff hΦ.contDiff p hDG
    (by simpa only [eD] using hdet)
  rw [(realSecondTensor_eventuallyEq hecomp).eq_of_nhds,eD,ep,
    (realSecondTensor_eventuallyEq heG).eq_of_nhds] at hh
  exact hh

end ClosedSurfaceR4.RealModes
namespace ClosedSurfaceR4
open SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem compact_overlap_secondTensor_bound {K : Set M} (hK : IsCompact K) (q p : M)
    (hKp : K ⊆ (coordinateChart p).source) (hKq : K ⊆ (coordinateChart q).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ a ∈ K, Function.Injective (fderiv ℝ (coordinateMap F q) (coordinateChart q a)) →
      ‖realSecondTensor (coordinateMap F p) (coordinateChart p a)‖ ≤
        C*‖realSecondTensor (coordinateMap F q) (coordinateChart q a)‖ := by
  obtain ⟨d,C,hd,hC,hbound⟩ := coordinateTransition_compact_bounds q p
    (coordinateChart_compact_image hK p hKp) (coordinateChart_image_overlap q p hKp hKq)
  refine ⟨4 * C ^ 2,by positivity,?_⟩
  intro F hF a ha hI
  have hx := coordinateTransition_mem_chart q p (hKp ha) (hKq ha)
  have hy := coordinateTransition_apply_chart q p (hKp ha)
  have hb := hbound (coordinateChart p a) (mem_image_of_mem _ ha)
  have hdet : coordDet (fderiv ℝ (coordinateTransition q p) (coordinateChart p a)) ≠ 0 :=
    abs_pos.mp (hd.trans_le hb.1)
  have htarget : coordinateTransition q p (coordinateChart p a) ∈ coordinateDomain q := by
    rw [hy,← coordinateChart_target]
    exact (coordinateChart q).map_source (hKq ha)
  have hh := norm_realSecondTensor_comp_on (coordinateTransition q p).open_source
    (coordinateDomain_open q) (coordinateMap_smoothOn hF q) (coordinateTransition_smoothOn q p)
    hx htarget (by simpa only [hy,coordDeriv] using gramDet_ne_zero_of_injective _ hI) hdet
  rw [(realSecondTensor_eventuallyEq (coordinateMap_transition_eventuallyEq F q p hx)).eq_of_nhds,
    hy] at hh
  calc
    _ ≤ 4*‖realSecondTensor (coordinateMap F q) (coordinateChart q a)‖*
        ‖fderiv ℝ (coordinateTransition q p) (coordinateChart p a)‖^2 := hh
    _ ≤ 4*‖realSecondTensor (coordinateMap F q) (coordinateChart q a)‖ * C ^ 2 := by gcongr; exact hb.2
    _ = _ := by ring

end ClosedSurfaceR4

end

end OAI
