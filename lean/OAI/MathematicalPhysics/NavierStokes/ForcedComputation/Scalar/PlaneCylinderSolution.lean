import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCylinderComponents
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneFluidBounds

namespace OAI

/-! The scalar existence input supplies a full classical cylinder solution
once the prescribed horizontal drift has strong L2 regularity. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem GlobalPlaneScalarSolution.cylinder_h2 (hE : PlaneScalarExistence)
    {ν : ℝ} (hν : 0 < ν) {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t, 0 ≤ t → ∀ x, 0 ≤ h t x)
    (haL2 : ∀ T, 0 ≤ T → ∀ j, PlaneCInH2 (fun t x => a t x j) (Icc 0 T))
    (T : ℝ) (hT : 0 ≤ T) (i : Fin 3) :
    CylinderCInH2 (fun t x => triangularVelocity a w (t, x) i) (Icc 0 T) := by
  have hinc : Icc (0 : ℝ) T ⊆ Icc 0 (T+1) := fun _ ht => ⟨ht.1, by linarith [ht.2]⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hs := ((hw (T+1) (by linarith)).cInH2 hE (by linarith) hν ha hh hc
      (fun t ht x => hpos t ht.1 x)).scalarPlaneLift
        (fun t ht => (hw (T+1) (by linarith)).slice_smooth ht)
    apply (hs.mono hinc).congr_slices
    intro t _
    funext x
    exact (triangularVelocity_third a w t x).symm
  · have hs := (haL2 T hT j).scalarPlaneLift (fun t _ =>
      ((contDiff_apply ℝ ℝ j).comp ha).comp (contDiff_const.prodMk contDiff_id))
    apply hs.congr_slices
    intro t _
    funext x
    exact (triangularVelocity_horizontal_component a w t x j).symm

theorem GlobalPlaneScalarSolution.cylinder_c1 (hE : PlaneScalarExistence)
    {ν : ℝ} (hν : 0 < ν) {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t, 0 ≤ t → ∀ x, 0 ≤ h t x)
    (haL2 : ∀ T, 0 ≤ T → ∀ j, PlaneC1L2 (fun t x => a t x j)
      (planeTemporalDerivative (fun t x => a t x j)) (Icc 0 T))
    (T : ℝ) (hT : 0 ≤ T) (i : Fin 3) :
    CylinderC1L2
      (fun t => cylinderPullback (fun x => triangularVelocity a w (t, x) i))
      (fun t => cylinderPullback (fun x => ShearFlows.initialTimeDerivative (triangularVelocity a w) t x i))
      (Icc 0 T) := by
  have hinc : Icc (0 : ℝ) T ⊆ Icc 0 (T+1) := fun _ ht => ⟨ht.1, by linarith [ht.2]⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hs := ((hw (T+1) (by linarith)).c1L2 hE (by linarith) hν ha hh hc
      (fun t ht x => hpos t ht.1 x)).cylinder
    apply (hs.mono hinc).congr_slices
    · intro t _
      funext y
      change w t y.1 = triangularVelocity a w (t, atHeight y.1 y.2) 2
      simp only [triangularVelocity_third, horizontalLinear_eq, atHeight_horizontal]
    · intro t ht
      funext y
      change planeTimeDerivative ν a h w t y.1 =
        ShearFlows.initialTimeDerivative (triangularVelocity a w) t (atHeight y.1 y.2) 2
      simp only [hw.initialTimeDerivative_vertical ha ht.1, horizontalLinear_eq,
        atHeight_horizontal]
  · apply (haL2 T hT j).cylinder.congr_slices
    · intro t _
      funext y
      simp only [cylinderPullback, triangularVelocity_horizontal_component,
        horizontalLinear_eq, atHeight_horizontal]
    · intro t ht
      funext y
      simp only [cylinderPullback, hw.initialTimeDerivative_horizontal ha ht.1,
        horizontalLinear_eq, atHeight_horizontal]

theorem GlobalPlaneScalarSolution.cylinder_solution (hE : PlaneScalarExistence)
    {ν : ℝ} (hν : 0 < ν) {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t, 0 ≤ t → ∀ x, 0 ≤ h t x)
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    (ha0 : ∀ x, a 0 x = 0)
    (haL2 : ∀ T, 0 ≤ T → ∀ j,
      PlaneCInH2 (fun t x => a t x j) (Icc 0 T) ∧
      PlaneC1L2 (fun t x => a t x j) (planeTemporalDerivative (fun t x => a t x j)) (Icc 0 T)) :
    IsCylinderClassicalSolution ν (triangularForce ν a h)
      (triangularVelocity a w) (fun _ => 0) where
  regularity := hw.classicalRegularity ha hh
  periodic_u t _ := triangularVelocity_vertically_periodic a w t
  periodic_p _ _ _ _ := rfl
  initial := triangularVelocity_plane_initial hw ha0
  divergence_zero t ht x := triangularVelocity_plane_divergence hw ha hdiv ht x
  equation t ht x := by
    simp only [gradient_constant, neg_zero, zero_add]
    exact triangularVelocity_plane_equation hw ha ht x
  velocity_h2 := hw.cylinder_h2 hE hν ha hh hc hpos (fun T hT j => (haL2 T hT j).1)
  velocity_c1 := hw.cylinder_c1 hE hν ha hh hc hpos (fun T hT j => (haL2 T hT j).2)
  pressure_h1 T _ := cylinderCInH1_zero (Icc 0 T)
  bounded T hT := (hw T hT).velocity_gradient_bound hT ha hc

end ForcedComputation.VelocityDetector

end

end OAI
