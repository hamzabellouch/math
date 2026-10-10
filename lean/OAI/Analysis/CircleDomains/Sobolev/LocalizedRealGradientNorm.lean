import OAI.Analysis.CircleDomains.Sobolev.RealGradientNorm
import OAI.Analysis.CircleDomains.Selection.PhysicalRealCoordinate

namespace OAI

/-! Exact gradient norm transport on measurable subsets of the physical
chart, used when excluding the permitted penalty region. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem real_chart_partial_eLpNorm_on
    {D S : Set (ℝ × ℝ)} (hD : IsOpen D) (hS : MeasurableSet S) (hSD : S ⊆ D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    (i : Fin 2)
    (hi : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' S))) :
    eLpNorm (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
        (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict S) =
      eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
        2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' S)) := by
  have hmp : MeasurePreserving euclideanPlaneCoordinates.symm (volume.restrict S)
      (volume.restrict (euclideanPlaneCoordinates ⁻¹' S)) := by
    convert euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage
      (hS.preimage euclideanPlaneCoordinates.continuous.measurable) using 1
    congr 1
  have heq : (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
      (if i = 0 then (1, 0) else (0, 1))) =ᵐ[volume.restrict S]
      (fun p => (fderiv ℝ w (euclideanPlaneCoordinates.symm p)) (EuclideanSpace.single i 1)) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    exact real_chart_partial_derivative hD hw (hSD hp) i
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_comp_measurePreserving hi.aestronglyMeasurable hmp


attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem physical_coordinate_partial_eLpNorm_on
    {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (w : EuclideanPlane → ℝ)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain))
    (Q : PhysicalRealCoordinate d π) (hQ : Q.quotient = quotientPlaneRepresentative d w)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hSD : S ⊆ FiniteTransfer.realChartDomain d.physicalDomain)
    (i : Fin 2)
    (hi : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' S))) :
    eLpNorm (fun p => (fderiv ℝ Q.physical p)
        (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict S) =
      eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
        2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' S)) := by
  let D := FiniteTransfer.realChartDomain d.physicalDomain
  have hD : IsOpen D := FiniteTransfer.isOpen_realChartDomain hG
  have hq : EqOn Q.physical (w ∘ euclideanPlaneCoordinates.symm) D := by
    intro p hp
    let x := euclideanPlaneCoordinates.symm p
    have hx : x ∈ physicalPlaneDomain d.physicalDomain := by
      change (Complex.equivRealProdCLM.symm p : Sphere) ∈ d.physicalDomain at hp
      change (Complex.equivRealProdCLM.symm (euclideanPlaneCoordinates x) : Sphere) ∈ d.physicalDomain
      simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using hp
    have hpull := Q.pullback (complexPlaneCoordinates x) hx
    have hpx : Complex.equivRealProdCLM (complexPlaneCoordinates x) = p := by
      simp [complexPlaneCoordinates, x]
    rw [hpx, hQ] at hpull
    exact hpull.trans (quotientPlaneRepresentative_plane d w π he hx)
  have heq : (fun p => (fderiv ℝ Q.physical p) (if i = 0 then (1, 0) else (0, 1)))
      =ᵐ[volume.restrict S] (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
        (if i = 0 then (1, 0) else (0, 1))) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    have hlocal : Q.physical =ᶠ[𝓝 p] w ∘ euclideanPlaneCoordinates.symm := by
      filter_upwards [hD.mem_nhds (hSD hp)] with y hy using hq hy
    rw [hlocal.fderiv_eq]
  rw [eLpNorm_congr_ae heq]
  exact real_chart_partial_eLpNorm_on hD hS hSD hw i hi

end CircleDomainRigidity

end

end OAI
