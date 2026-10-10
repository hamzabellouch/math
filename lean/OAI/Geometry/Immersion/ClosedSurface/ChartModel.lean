import OAI.Geometry.Immersion.ClosedSurface.RealModes

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold


def planeCoordinates : Plane ≃L[ℝ] Base :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans
    (ContinuousLinearEquiv.piFinTwo ℝ (fun _ => ℝ))
def spaceCoordinates : Space ≃L[ℝ] RVec 4 := EuclideanSpace.equiv (Fin 4) ℝ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def coordinateDomain (p : M) : Set Base :=
  planeCoordinates.symm ⁻¹' (extChartAt planeModel p).target

def coordinateCenter (p : M) : Base := planeCoordinates (extChartAt planeModel p p)

def coordinateMap (F : M → Space) (p : M) : RField 4 :=
  spaceCoordinates ∘ F ∘ (extChartAt planeModel p).symm ∘ planeCoordinates.symm

lemma coordinateDomain_open (p : M) : IsOpen (coordinateDomain p) := by
  apply IsOpen.preimage planeCoordinates.symm.continuous
  simpa [extChartAt_target, planeModel] using (chartAt Plane p).open_target

lemma coordinateCenter_mem (p : M) : coordinateCenter p ∈ coordinateDomain p := by
  simp [coordinateCenter, coordinateDomain]

lemma coordinateMap_at_center (F : M → Space) (p : M) :
    coordinateMap F p (coordinateCenter p) = spaceCoordinates (F p) := by
  simp [coordinateMap, coordinateCenter]

lemma coordinateMap_smoothOn [IsManifold planeModel ∞ M] {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M) :
    ContDiffOn ℝ ∞ (coordinateMap F p) (coordinateDomain p) := by
  apply ContMDiffOn.contDiffOn
  have hChart := contMDiffOn_extChartAt_symm (I := planeModel) (n := (∞ : ℕ∞ω)) p
  have h1 := hF.comp_contMDiffOn hChart
  have h2 := spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn h1
  exact h2.comp planeCoordinates.symm.contDiff.contMDiff.contMDiffOn
    (fun x hx => hx)

lemma mfderiv_coordinateMap_center {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M) :
    fderiv ℝ (coordinateMap F p) (coordinateCenter p) =
      spaceCoordinates.toContinuousLinearMap.comp
        ((mfderiv planeModel spaceModel F p).comp
          planeCoordinates.symm.toContinuousLinearMap) := by
  have hd := (hF p).mdifferentiableAt (by simp)
  have heq : mfderiv planeModel spaceModel F p =
      fderiv ℝ (F ∘ (extChartAt planeModel p).symm) (extChartAt planeModel p p) := by
    simpa [writtenInExtChartAt, planeModel, spaceModel, chartAt_self_eq,
      differentiableWithinAt_univ] using hd.mfderiv_abuse
  have h0 : DifferentiableAt ℝ (F ∘ (extChartAt planeModel p).symm)
      (extChartAt planeModel p p) := by
    simpa [writtenInExtChartAt, planeModel, spaceModel, chartAt_self_eq,
      differentiableWithinAt_univ] using
      hd.differentiableWithinAt_writtenInExtChartAt
  have h1 : HasFDerivAt (spaceCoordinates ∘ F ∘ (extChartAt planeModel p).symm)
      (spaceCoordinates.toContinuousLinearMap.comp
        (fderiv ℝ (F ∘ (extChartAt planeModel p).symm) (extChartAt planeModel p p)))
      (planeCoordinates.symm (coordinateCenter p)) := by
    simpa [coordinateCenter] using spaceCoordinates.hasFDerivAt.comp
      (extChartAt planeModel p p) h0.hasFDerivAt
  have hc := h1.comp (coordinateCenter p) planeCoordinates.symm.hasFDerivAt
  rw [heq]
  have hc' := hc.fderiv
  simp only [coordinateMap, Function.comp_assoc, ContinuousLinearMap.comp_assoc] at hc' ⊢
  exact hc'

lemma coordinateMap_immersion_center {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M)
    (hImm : Function.Injective (mfderiv planeModel spaceModel F p)) :
    Function.Injective (fderiv ℝ (coordinateMap F p) (coordinateCenter p)) := by
  rw [mfderiv_coordinateMap_center hF p]
  exact spaceCoordinates.injective.comp (hImm.comp planeCoordinates.symm.injective)

lemma spaceCoordinates_dot (v w : Space) :
    spaceCoordinates v ⬝ᵥ spaceCoordinates w = inner ℝ v w := by
  simp [spaceCoordinates, dotProduct, PiLp.inner_apply, mul_comm]

lemma coordinateMetric_at_center {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M) (v w : Base) :
    (fderiv ℝ (coordinateMap F p) (coordinateCenter p) v) ⬝ᵥ
      (fderiv ℝ (coordinateMap F p) (coordinateCenter p) w) =
      inner ℝ (mfderiv planeModel spaceModel F p (planeCoordinates.symm v))
        (mfderiv planeModel spaceModel F p (planeCoordinates.symm w)) := by
  rw [mfderiv_coordinateMap_center hF p]
  exact spaceCoordinates_dot _ _

end ClosedSurfaceR4

end

end OAI
