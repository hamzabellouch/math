import OAI.Analysis.CircleDomains.Sobolev.RealGradientTransport
import OAI.Analysis.CircleDomains.Sobolev.MeasurableCircleGradient
import OAI.Analysis.CircleDomains.Topology.CircleChainRule

namespace OAI

/-! Measurable real-plane representatives of smooth circle coordinates,
with the exact original L2 partial norms. No global real lift is used. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_real_circle_representative
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) (w : EuclideanPlane → UnitAddCircle)
    (hw : SmoothCircleOn w (euclideanPlaneCoordinates ⁻¹' D))
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv w x (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) :
    ∃ f : (ℝ × ℝ) → UnitAddCircle, Measurable f ∧ Measurable (circleGradient f) ∧
      SmoothCircleOn f D ∧ MemLp (circleGradient f) 2 (volume.restrict D) ∧
      (∀ i : Fin 2, eLpNorm (fun p => circleFDeriv f p
          (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict D) =
        eLpNorm (fun x => circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) ∧
      ∀ p ∈ D, f p = w (euclideanPlaneCoordinates.symm p) := by
  let q := euclideanPlaneCoordinates.symm
  let f₁ := w ∘ q
  have hΩ := hD.preimage euclideanPlaneCoordinates.continuous
  have hqin (p : ℝ × ℝ) (hp : p ∈ D) : q p ∈ euclideanPlaneCoordinates ⁻¹' D := by
    simpa only [q, mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hs : SmoothCircleOn f₁ D := by
    intro p hp a ha
    exact (hw (q p) (hqin p hp) a ha).comp p q.contDiff.contDiffAt
  have hmp : MeasurePreserving q (volume.restrict D)
      (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
    convert euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage hΩ.measurableSet using 1
    congr 1
  have hpartial (i : Fin 2) (p : ℝ × ℝ) (hp : p ∈ D) :
      circleFDeriv f₁ p (if i = 0 then (1, 0) else (0, 1)) =
        circleFDeriv w (q p) (EuclideanSpace.single i 1) := by
    rw [circleFDeriv_comp hΩ hw q.differentiableAt (hqin p hp), q.fderiv]
    change circleFDeriv w (q p) (euclideanPlaneCoordinates.symm
      (if i = 0 then (1, 0) else (0, 1))) = _
    rw [euclideanPlaneCoordinates_symm_axis]
  let f : (ℝ × ℝ) → UnitAddCircle := D.piecewise f₁ (fun _ => 0)
  have heq (p : ℝ × ℝ) (hp : p ∈ D) : f =ᶠ[𝓝 p] f₁ := by
    filter_upwards [hD.mem_nhds hp] with x hx
    exact piecewise_eq_of_mem D _ _ hx
  have hmeas : Measurable f := hs.continuousOn.measurable_piecewise continuousOn_const hD.measurableSet
  have hsf : SmoothCircleOn f D := by
    apply smoothCircleOn_iff_local_lifts.mpr
    intro p hp
    obtain ⟨u, hu, hproj⟩ := smoothCircleOn_iff_local_lifts.mp hs p hp
    exact ⟨u, hu, hproj.trans (heq p hp).symm⟩
  have hder (i : Fin 2) : (fun p => circleFDeriv f p
      (if i = 0 then (1, 0) else (0, 1))) =ᵐ[volume.restrict D]
      (fun p => circleFDeriv w (q p) (EuclideanSpace.single i 1)) := by
    filter_upwards [ae_restrict_mem hD.measurableSet] with p hp
    have he := (heq p hp)
    have hf' : circleFDeriv f p = circleFDeriv f₁ p := by
      have hu : ContinuousAt (circleBranch f₁ (circleCut f₁ p)) p :=
        (hs p hp _ (circleCut_ne f₁ p)).continuousAt
      have hlift : (fun x => (circleBranch f₁ (circleCut f₁ p) x : UnitAddCircle)) =ᶠ[𝓝 p] f :=
        (show (fun x => (circleBranch f₁ (circleCut f₁ p) x : UnitAddCircle)) =ᶠ[𝓝 p] f₁ from
          Eventually.of_forall (coe_circleBranch f₁ _)).trans he.symm
      exact circleFDeriv_eq_lift
        ((hs.continuousOn.continuousAt (hD.mem_nhds hp)).congr he.symm) hu hlift
    rw [hf']
    exact hpartial i p hp
  have hi (i : Fin 2) : MemLp (fun p => circleFDeriv f p
      (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict D) :=
    ((henergy i).comp_measurePreserving hmp).ae_eq (hder i).symm
  refine ⟨f, hmeas, measurable_circleGradient hmeas, hsf,
    memLp_prod_iff.mpr ⟨hi 0, hi 1⟩, ?_, fun p hp => (heq p hp).self_of_nhds⟩
  intro i
  rw [eLpNorm_congr_ae (hder i)]
  exact eLpNorm_comp_measurePreserving (henergy i).aestronglyMeasurable hmp

end CircleDomainRigidity

end

end OAI
