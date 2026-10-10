import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingScalarDetector
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDriftL2
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCylinderSolution
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderPressureUniqueness

namespace OAI

/-! The scalar computation detector is a full classical Navier–Stokes
solution, unique in the cylinder comparison class. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set MeasureTheory
open scoped ContDiff

/-- The observed mass integrates over the entire unit vertical period. -/
def upperCylinderMass (u : Velocity) (t : ℝ) : ℝ :=
  ∫ x in upperHalfPlane, ∫ z, u (t, atHeight x z) 2 ∂verticalPeriodMeasure

theorem upperCylinderMass_triangular (a : ℝ → Plane → Plane) (w : ℝ → Plane → ℝ)
    (t : ℝ) : upperCylinderMass (triangularVelocity a w) t =
      ∫ x in upperHalfPlane, w t x := by
  simp only [upperCylinderMass, triangularVelocity_third, horizontalLinear_eq,
    atHeight_horizontal, integral_const, probReal_univ, one_smul]

def WholePlaneDetection (ν : ℝ) (f : Velocity) (I : Alternating.MachineInput) : Prop :=
  ∃ u : Velocity,
    (∀ T, 0 ≤ T → ContDiffOn ℝ ∞ u (timeCylinder T)) ∧
    IsCylinderClassicalSolution ν f u (fun _ => 0) ∧
    (∀ v q, IsCylinderClassicalSolution ν f v q →
      ∀ t, 0 ≤ t → ∀ x, v (t,x) = u (t,x) ∧ q (t,x) = 0) ∧
    (∀ t, 0 ≤ t → ∀ x, 0 ≤ u (t,atHeight x 0) 2) ∧
    (∀ t, 0 ≤ t → Integrable (fun x => u (t,atHeight x 0) 2)) ∧
    (∀ t, 0 ≤ t → (∫ x, u (t,atHeight x 0) 2) = smoothRamp 0 1 t) ∧
    ((∃ t : ℝ, 0 ≤ t ∧ 1 / 2 < upperCylinderMass u t) ↔
      Alternating.Halts I)

theorem expanding_fluid_detection (hE : PlaneScalarExistence)
    (hEnergy : CylinderLocalEnergyIdentity)
    (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {ν C σ D K : ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K) (hcoef : ν * C ≤ σ * 3000)
    (hΔ : ∀ x, |scalarLaplacian massCutoff x| ≤ C) :
    let m := initialWordLength I
    let blank := recorderBlank I.1
    let p := configurationCenter I.1 hI.1 blank m σ D K 0 (finiteInitializedRecorder I hI)
    let a := expandingDrift I.1 hI.1 blank m σ D K
    let f := triangularForce ν a (unitImpulse p)
    WholePlaneDetection ν f I := by
  dsimp only [WholePlaneDetection]
  let m := initialWordLength I
  let blank := recorderBlank I.1
  let p := configurationCenter I.1 hI.1 blank m σ D K 0 (finiteInitializedRecorder I hI)
  let a := expandingDrift I.1 hI.1 blank m σ D K
  obtain ⟨w, hw, hn, hi, hm, hdetect⟩ := expanding_scalar_detection hE I hI hν hC
    hσ hD hK hcoef hΔ
  have ha := expandingDrift_smooth I.1 hI.1 blank m hσ hD hK
  have hc := expandingDrift_compact_coefficients I.1 hI.1 blank m hσ hD hK p
  have hsol : IsCylinderClassicalSolution ν (triangularForce ν a (unitImpulse p))
      (triangularVelocity a w) (fun _ => 0) :=
    hw.cylinder_solution hE hν ha (unitImpulse_smooth p) hc
      (fun t _ x => unitImpulse_nonneg p t x)
      (expandingDrift_divergence I.1 hI.1 blank m hσ hD hK)
      (fun x => expandingDrift_initial I.1 hI.1 blank m hσ hD hK (by norm_num) x)
      (fun T _ j => expandingDrift_component_regularity I.1 hI.1 blank m hσ hD hK T j)
  refine ⟨triangularVelocity a w, ?_, hsol, cylinder_classical_unique hEnergy hν hsol,
    ?_, ?_, ?_, ?_⟩
  · intro T hT
    exact (hw T hT).triangularVelocity_plane_smoothOn ha
  · simpa only [triangularVelocity_third, horizontalLinear_eq, atHeight_horizontal] using hn
  · simpa only [triangularVelocity_third, horizontalLinear_eq, atHeight_horizontal] using hi
  · simpa only [triangularVelocity_third, horizontalLinear_eq, atHeight_horizontal] using hm
  · simpa only [upperCylinderMass_triangular] using hdetect

end ForcedComputation.ExpandingDetector

end

end OAI
