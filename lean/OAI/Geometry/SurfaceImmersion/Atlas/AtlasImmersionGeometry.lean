import OAI.Geometry.SurfaceImmersion.Correction.GoodSmoothingAtlas
import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionJets
import OAI.Geometry.Immersion.ClosedSurface.AtlasPhases
import OAI.Geometry.Immersion.ClosedSurface.MetricBounds

namespace OAI

/-! Local good-phase geometry in any covering chart gives the intrinsic
immersion and nonzero second-form hypotheses for the next primitive. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology Matrix
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateMap_injective_of_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (q : M) {x : SmallModes.Base} (hx : x ∈ coordinateDomain q) :
    Function.Injective (fderiv ℝ (coordinateMap F q) x) := by
  have hi := ((coordinateInverse_smoothOn q) x hx).contMDiffAt
    ((coordinateDomain_open q).mem_nhds hx)
  have hm := (hF (coordinateInverse q x)).mdifferentiableAt (by simp)
  have hic := hi.mdifferentiableAt (by simp)
  have hd := mfderiv_comp x hm hic
  rw [mfderiv_eq_fderiv] at hd
  have hs : DifferentiableAt ℝ (F ∘ coordinateInverse q) x :=
    (hm.comp x hic).differentiableAt
  change Function.Injective (fderiv ℝ (spaceCoordinates ∘ (F ∘ coordinateInverse q)) x)
  rw [fderiv_comp x spaceCoordinates.differentiableAt hs,spaceCoordinates.fderiv,hd]
  exact spaceCoordinates.injective.comp ((hI _).comp (coordinateInverse_mfderiv_injective q hx))

lemma nonzero_secondForm_of_chart_good {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M)
    (hp : p ∈ (coordinateChart q).source)
    (hI : Function.Injective (fderiv ℝ (coordinateMap F q) (coordinateChart q p)))
    {ξ : SmallModes.Base}
    (hg : Good (realSecondTensor (coordinateMap F q) (coordinateChart q p)) ξ) :
    ∃ v w : SmallModes.Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0 := by
  let B := realSecondTensor (coordinateMap F q) (coordinateChart q p)
  have hB : B ≠ 0 := by
    intro h
    exact hg.2 (by simp only [B,h,secondQuadratic,Pi.zero_apply,smul_zero,add_zero])
  have hbn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hqn : 0 < ‖secondQuadratic B (-ξ.2,ξ.1)‖ := norm_pos_iff.mpr hg.2
  let ε := ‖secondQuadratic B (-ξ.2,ξ.1)‖/‖B‖
  have hε : 0 < ε := div_pos hqn hbn
  have hm : ε*‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖ :=
    le_of_eq (div_mul_cancel₀ _ hbn.ne')
  have hpp : p ∈ (coordinateChart p).source := by
    rw [coordinateChart_source]
    exact mem_chart_source Plane p
  have hx : coordinateCenter p ∈ (coordinateTransition q p).source := by
    have hh := coordinateTransition_mem_chart q p hpp hp
    simpa only [coordinateChart_apply,chartCoordinates_center] using hh
  obtain ⟨d,C,hd,hC,hbound⟩ := coordinateTransition_compact_bounds q p
    (isCompact_singleton (x := coordinateCenter p)) (singleton_subset_iff.mpr hx)
  have hb := hbound (coordinateCenter p) (mem_singleton _)
  have he : coordinateTransition q p (coordinateCenter p) = coordinateChart q p := by
    have hh := coordinateTransition_apply_chart q p hpp
    simpa only [coordinateChart_apply,chartCoordinates_center] using hh
  have hD := gramDet_ne_zero_of_injective (fderiv ℝ (coordinateMap F q) (coordinateChart q p)) hI
  have ht := actual_chart_phase_margin hF q p hx ξ hd hC hε
    (by simpa only [he,coordDeriv] using hD) hb.1 hb.2
    (by simpa only [he] using hB) (by simpa only [he] using hm)
  have hn : realSecondTensor (coordinateMap F p) (coordinateCenter p) ≠ 0 := ht.2.2.2
  by_contra! hzero
  apply hn
  funext i
  fin_cases i
  · exact hzero dx dx
  · exact hzero dx dy
  · exact hzero dy dy

namespace FiniteOrderSmoothing.SmoothingAtlas
open JetPolynomial
variable [CompactSpace M] (A : SmoothingAtlas M)

lemma immersion_of_planeRead_injective (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {p : M}
    (hp : p ∈ tsupport (A.weight i))
    (hI : Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p)))) :
    Function.Injective (mfderiv planeModel spaceModel F p) := by
  have hread : Function.Injective (fderiv ℝ (A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p))) := by
    have he := (spaceCoordinates.hasFDerivAt.comp (planeCoordinateIsometry (chart (i : M) p))
      ((A.vectorPlaneRead_smooth i hF).differentiable (by simp)
        (planeCoordinateIsometry (chart (i : M) p))).hasFDerivAt).fderiv
    rw [he] at hI
    intro v w hv
    apply hI
    exact congrArg spaceCoordinates hv
  change Function.Injective (surfaceDifferential F p)
  rw [A.vectorPlaneRead_differential i hF hp]
  exact hread.comp (planeCoordinateIsometry.injective.comp
    ((chart_mdifferentiable (i : M)).mfderiv_injective (A.weight_support i hp)))

theorem geometry_of_chartwise_good {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hgeom : ∀ p : M, ∃ i : A.centers, p ∈ tsupport (A.weight i) ∧
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ∧
      ∃ ξ : SmallModes.Base,
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
          (planeCoordinateIsometry (chart (i : M) p))) ξ) :
    (∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) ∧
    (∀ p, ∃ v w : SmallModes.Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0) := by
  constructor
  · intro p
    obtain ⟨i,hp,hi,_⟩ := hgeom p
    exact A.immersion_of_planeRead_injective i hF hp hi
  · intro p
    obtain ⟨i,hp,hi,ξ,hg⟩ := hgeom p
    have he := A.vectorPlaneRead_eventually_coordinateMap F i (houter i) hp
    have hpoint : coordinateChart (i : M) p = planeCoordinateIsometry (chart (i : M) p) := by
      rw [planeCoordinateIsometry_chart]
      rfl
    have hI : Function.Injective (fderiv ℝ (coordinateMap F (i : M))
        (coordinateChart (i : M) p)) := by
      rw [hpoint,← he.fderiv_eq]
      exact hi
    have hgood : Good (realSecondTensor (coordinateMap F (i : M))
        (coordinateChart (i : M) p)) ξ := by
      rw [hpoint,← (realSecondTensor_eventuallyEq he).eq_of_nhds]
      exact hg
    exact nonzero_secondForm_of_chart_good hF (i : M) p
      (by simpa [coordinateChart_source,chart] using A.weight_support i hp) hI hgood

end FiniteOrderSmoothing.SmoothingAtlas
end ClosedSurfaceR4

end

end OAI
