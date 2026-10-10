import OAI.Geometry.SurfaceImmersion.Correction.AdaptedSmoothingAtlas
import OAI.Geometry.Immersion.ClosedSurface.PhasePatches
import OAI.Geometry.Immersion.ClosedSurface.PhaseStock
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadDifferential

namespace OAI

/-! A smoothing atlas subordinate to actual good-phase neighborhoods. -/
noncomputable section
open Set Manifold Filter TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def PhasePatch.phaseBasis {F : M → Space} {H : Base → PhaseMean.Tensor} {p : M}
    (P : PhasePatch F H p) : PhaseBasis where
  ξ := P.ξ
  Q := P.Q
  decomposition := P.decomposition
  nonzero := fun j => ((P.admissible _ P.centerO).2.2.1 j).1

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

omit [IsManifold planeModel ∞ M] in
lemma planeCoordinateIsometry_chart (p x : M) :
    planeCoordinateIsometry (chart p x) = planeCoordinates (chartAt Plane p x) := rfl

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_chart_symm (F : M → Space) (p : M) (x : SmallModes.Base) :
    coordinateMap F p x = spaceCoordinates (F ((chart p).symm (planeCoordinateIsometry.symm x))) := rfl

variable [T2Space M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [T2Space M] [CompactSpace M] in
/-- Locally constant outer cutoffs identify the entire coordinate germ on
the original weight support, and hence every derivative used by the phases. -/
lemma vectorPlaneRead_eventually_coordinateMap
    (F : M → Space) (i : A.centers)
    (houter : ∀ x ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    (spaceCoordinates ∘ A.vectorPlaneRead i F) =ᶠ[
      𝓝 (planeCoordinateIsometry (chart (i : M) p))] coordinateMap F (i : M) := by
  let x := planeCoordinateIsometry (chart (i : M) p)
  let inv : SmallModes.Base → M := fun z => (chart (i : M)).symm (planeCoordinateIsometry.symm z)
  have hpS := A.weight_support i hp
  have hinv : inv x = p := by
    dsimp [inv,x]
    rw [LinearIsometryEquiv.symm_apply_apply,(chart (i : M)).left_inv hpS]
  have hc : ContinuousAt inv x := by
    apply ContinuousAt.comp
    · apply (chart (i : M)).continuousAt_symm
      simpa only [x,LinearIsometryEquiv.symm_apply_apply] using (chart (i : M)).map_source hpS
    · exact planeCoordinateIsometry.symm.continuous.continuousAt
  have ht : Tendsto inv (𝓝 x) (𝓝 p) := by simpa only [ContinuousAt,hinv] using hc
  have ho : ∀ᶠ z in 𝓝 x, A.outer i (inv z) = 1 := (houter p hp).comp_tendsto ht
  have htarget : ∀ᶠ z in 𝓝 x,
      planeCoordinateIsometry.symm z ∈ (chart (i : M)).target :=
    ((chart (i : M)).open_target.preimage planeCoordinateIsometry.symm.continuous).mem_nhds
      (by simpa only [Set.mem_preimage,x,LinearIsometryEquiv.symm_apply_apply] using
        (chart (i : M)).map_source hpS)
  filter_upwards [ho,htarget] with z hz htgt
  change spaceCoordinates (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm z)) = _
  rw [localize,indicator_of_mem htgt]
  change spaceCoordinates (A.outer i (inv z)^2 • F (inv z)) = _
  rw [hz,one_pow,one_smul]
  exact (coordinateMap_chart_symm F (i : M) z).symm

end SmoothingAtlas

/-- Good phase patches and a smoothing atlas share the same actual centers.
All local immersion, positivity and pure/mixed phase conditions are inherited
by the globally smooth coordinate readings on their compact supports. -/
theorem exists_good_smoothingAtlas {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (hB : ∀ p, ∃ v w : SmallModes.Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0)
    (H : M → SmallModes.Base → PhaseMean.Tensor)
    (hH : ∀ p, ContinuousAt (H p) (coordinateCenter p))
    (hH0 : ∀ p, 0 < H p (coordinateCenter p) 0)
    (hHdet : ∀ p, 0 < H p (coordinateCenter p) 0 * H p (coordinateCenter p) 2 -
      (H p (coordinateCenter p) 1)^2) :
    ∃ (A : SmoothingAtlas M) (P : ∀ p, PhasePatch F (H p) p),
      (∀ i : A.centers, tsupport (A.weight i) ⊆ (P (i : M)).V) ∧
      (∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1)) ∧
      ∀ (i : A.centers) (x : SmallModes.Base),
        x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ∧
        (∀ j, 0 < (P (i : M)).Q j (H (i : M) x)) ∧
        (∀ j, Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          ((P (i : M)).ξ j)) ∧
        (∀ j k, j ≠ k →
          Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
            ((P (i : M)).ξ j + (P (i : M)).ξ k) ∧
          Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
            ((P (i : M)).ξ j - (P (i : M)).ξ k)) := by
  classical
  let P : ∀ p, PhasePatch F (H p) p := fun p =>
    Classical.choice (exists_phasePatch hF p (hImm p) (hB p) (hH p) (hH0 p) (hHdet p))
  obtain ⟨A,hsub,houter⟩ := exists_smoothingAtlas_subordinate_locally_one
    (fun p => (P p).V) (fun p => (P p).openV) (fun p => (P p).centerV)
  refine ⟨A,P,hsub,houter,?_⟩
  intro i x hx
  change x ∈ planeCoordinateIsometry '' ((chart (i : M)) '' tsupport (A.weight i)) at hx
  rcases hx with ⟨y,⟨p,hp,rfl⟩,rfl⟩
  have hO : planeCoordinateIsometry (chart (i : M) p) ∈ (P (i : M)).O := by
    simpa only [planeCoordinateIsometry_chart] using (P (i : M)).mapsV p (hsub i hp)
  have he := A.vectorPlaneRead_eventually_coordinateMap F i (houter i) hp
  have hder := he.fderiv_eq (𝕜 := ℝ)
  have hsecond := (realSecondTensor_eventuallyEq he).eq_of_nhds
  have ha := (P (i : M)).admissible _ hO
  rw [← hder,← hsecond] at ha
  exact ha

end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
