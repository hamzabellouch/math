import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderSolution
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCompactH2
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCylinderL2
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularLift

namespace OAI

/-! Horizontal scalar lifts preserve the strong Sobolev conditions. Their
vertical derivatives vanish, and their horizontal derivatives are the
ordinary derivatives of the planar scalar. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set
open scoped ContDiff

def scalarPlaneLift (f : Plane → ℝ) : Space → ℝ := f ∘ horizontalLinear

theorem scalarPlaneLift_pullback (f : Plane → ℝ) :
    cylinderPullback (scalarPlaneLift f) = fun y => f y.1 := by
  funext y
  simp only [cylinderPullback, scalarPlaneLift, Function.comp_apply,
    horizontalLinear_eq, atHeight_horizontal]

theorem scalarPlaneLift_spatialD {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 2) :
    scalarSpatialD j.castSucc (scalarPlaneLift f) =
      scalarPlaneLift (PlanarHamiltonian.spatialD j f) := by
  funext x
  have hd := (hf.differentiable (by simp) (horizontalLinear x)).hasFDerivAt.comp x
    horizontalLinear.hasFDerivAt
  change fderiv ℝ (f ∘ horizontalLinear) x (basis j.castSucc) = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, horizontalLinear_basis]
  rfl

theorem scalarPlaneLift_verticalD {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    scalarSpatialD 2 (scalarPlaneLift f) = fun _ => 0 := by
  funext x
  have hd := (hf.differentiable (by simp) (horizontalLinear x)).hasFDerivAt.comp x
    horizontalLinear.hasFDerivAt
  change fderiv ℝ (f ∘ horizontalLinear) x (basis 2) = 0
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, horizontalLinear_basis_two, map_zero]

theorem CylinderContinuousL2.congr_slices {F G : ℝ → Plane × ℝ → ℝ} {S : Set ℝ}
    (hF : CylinderContinuousL2 F S) (hFG : ∀ t ∈ S, F t = G t) :
    CylinderContinuousL2 G S := by
  obtain ⟨U, hU, hUF⟩ := hF
  exact ⟨U, hU, fun t ht => by rw [← hFG t ht]; exact hUF t ht⟩

theorem CylinderC1L2.congr_slices {F G F' G' : ℝ → Plane × ℝ → ℝ} {S : Set ℝ}
    (hF : CylinderC1L2 F G S) (hFF : ∀ t ∈ S, F t = F' t)
    (hGG : ∀ t ∈ S, G t = G' t) : CylinderC1L2 F' G' S := by
  obtain ⟨U, V, hU, hV, hUV⟩ := hF
  refine ⟨U, V, hU, hV, ?_⟩
  intro t ht
  rw [← hFF t ht, ← hGG t ht]
  exact hUV t ht

theorem cylinderContinuousL2_zero (S : Set ℝ) :
    CylinderContinuousL2 (fun _ _ => 0) S :=
  ⟨fun _ => 0, continuousOn_const, fun _ _ => Lp.coeFn_zero ℝ 2 cylinderMeasure⟩

theorem PlaneContinuousL2.scalarPlaneLift {F : ℝ → Plane → ℝ} {S : Set ℝ}
    (hF : PlaneContinuousL2 F S) :
    CylinderContinuousL2 (fun t => cylinderPullback (scalarPlaneLift (F t))) S := by
  simpa only [scalarPlaneLift_pullback] using hF.cylinder

theorem PlaneCInH2.scalarPlaneLift {F : ℝ → Plane → ℝ} {S : Set ℝ}
    (hF : PlaneCInH2 F S) (hs : ∀ t ∈ S, ContDiff ℝ ∞ (F t)) :
    CylinderCInH2 (fun t => scalarPlaneLift (F t)) S := by
  refine ⟨hF.1.scalarPlaneLift, ?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · apply (cylinderContinuousL2_zero S).congr_slices
      intro t ht
      change (fun _ : Plane × ℝ => (0 : ℝ)) =
        cylinderPullback (scalarSpatialD 2 (VelocityDetector.scalarPlaneLift (F t)))
      rw [scalarPlaneLift_verticalD (hs t ht)]
      rfl
    · apply (hF.2.1 k).scalarPlaneLift.congr_slices
      intro t ht
      rw [scalarPlaneLift_spatialD (hs t ht)]
  · intro j k
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · apply (cylinderContinuousL2_zero S).congr_slices
      intro t ht
      change (fun _ : Plane × ℝ => (0 : ℝ)) =
        cylinderPullback (scalarSpatialD j (scalarSpatialD 2 (VelocityDetector.scalarPlaneLift (F t))))
      rw [scalarPlaneLift_verticalD (hs t ht)]
      funext y
      change (0 : ℝ) = fderiv ℝ (fun _ : Space => (0 : ℝ))
        (atHeight y.1 y.2) (basis j)
      rw [fderiv_const_apply]
      rfl
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · apply (cylinderContinuousL2_zero S).congr_slices
        intro t ht
        change (fun _ : Plane × ℝ => (0 : ℝ)) =
          cylinderPullback (scalarSpatialD 2
            (scalarSpatialD k'.castSucc (VelocityDetector.scalarPlaneLift (F t))))
        rw [scalarPlaneLift_spatialD (hs t ht),
          scalarPlaneLift_verticalD (PlanarHamiltonian.spatialD_smooth k' (hs t ht))]
        rfl
      · apply (hF.2.2 j' k').scalarPlaneLift.congr_slices
        intro t ht
        rw [scalarPlaneLift_spatialD (hs t ht),
          scalarPlaneLift_spatialD (PlanarHamiltonian.spatialD_smooth k' (hs t ht))]

end ForcedComputation.VelocityDetector

end

end OAI
