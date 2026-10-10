import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneSobolevL2
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderMeasure

namespace OAI

/-! Lifting planar L2 representatives to one vertical period. The lift is
an isometry because the vertical interval has measure one. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set

def planeCylinderLift : PlaneL2 →L[ℝ] CylinderL2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst
    (measurePreserving_fst (μ := (volume : Measure Plane))
      (ν := verticalPeriodMeasure))).toContinuousLinearMap

theorem planeCylinderLift_ae (u : PlaneL2) {f : Plane → ℝ}
    (hf : (fun x => u x) =ᵐ[volume] f) :
    (fun x => planeCylinderLift u x) =ᵐ[cylinderMeasure] fun x => f x.1 := by
  have hp := measurePreserving_fst (μ := (volume : Measure Plane))
    (ν := verticalPeriodMeasure)
  exact (Lp.coeFn_compMeasurePreserving u hp).trans
    (hp.quasiMeasurePreserving.ae_eq_comp hf)

theorem planeCylinderLift_norm (u : PlaneL2) : ‖planeCylinderLift u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u _

theorem PlaneContinuousL2.cylinder {F : ℝ → Plane → ℝ} {S : Set ℝ}
    (hF : PlaneContinuousL2 F S) :
    CylinderContinuousL2 (fun t x => F t x.1) S := by
  obtain ⟨U, hU, hUF⟩ := hF
  exact ⟨fun t => planeCylinderLift (U t),
    planeCylinderLift.continuous.comp_continuousOn hU,
    fun t ht => planeCylinderLift_ae (U t) (hUF t ht)⟩

theorem PlaneC1L2.cylinder {F G : ℝ → Plane → ℝ} {S : Set ℝ}
    (hF : PlaneC1L2 F G S) :
    CylinderC1L2 (fun t x => F t x.1) (fun t x => G t x.1) S := by
  obtain ⟨U, V, hU, hV, hUV⟩ := hF
  refine ⟨fun t => planeCylinderLift (U t), fun t => planeCylinderLift (V t),
    planeCylinderLift.continuous.comp_continuousOn hU,
    planeCylinderLift.continuous.comp_continuousOn hV, ?_⟩
  intro t ht
  obtain ⟨hu, hv, hd⟩ := hUV t ht
  refine ⟨planeCylinderLift_ae (U t) hu, planeCylinderLift_ae (V t) hv, ?_⟩
  exact planeCylinderLift.hasFDerivAt.comp_hasDerivWithinAt t hd

end ForcedComputation.VelocityDetector

end

end OAI
