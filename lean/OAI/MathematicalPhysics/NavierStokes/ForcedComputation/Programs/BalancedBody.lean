import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedStretch
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedPlanarProgram
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactTimeSupport

namespace OAI

/-! The repeated compact Euclidean field depends only on the machine. Its
fixed vertical cutoff leaves the planar computation on height zero exact. -/

noncomputable section
namespace ForcedComputation.BalancedBody
open ShearFlows Set PlanarHamiltonian Recorder.Planar
open scoped ContDiff

def verticalCutoff : ℝ → ℝ := closedCutoff (-2) (-1) 1 2

theorem verticalCutoff_smooth : ContDiff ℝ ∞ verticalCutoff :=
  closedCutoff_smooth _ _ _ _

theorem verticalCutoff_zero : verticalCutoff 0 = 1 :=
  closedCutoff_plateau (by norm_num) (by norm_num) (by constructor <;> norm_num)

def raw (M : Alternating.Machine) (hM : M.WellFormed) : Velocity :=
  CompactLift.velocity verticalCutoff (BalancedPlanar.bodyVelocity M hM)

def velocity (M : Alternating.Machine) (hM : M.WellFormed) : Velocity :=
  BalancedStretch.velocity (raw M hM)

def rawSupport : Set Space := Icc ![0, 0, -2] ![1, 1, 2]

def support : Set Space := BalancedStretch.stretch '' rawSupport

theorem rawSupport_compact : IsCompact rawSupport := isCompact_Icc

theorem support_compact : IsCompact support :=
  rawSupport_compact.image BalancedStretch.stretch.continuous

theorem raw_smooth (M : Alternating.Machine) (hM : M.WellFormed) :
    ContDiff ℝ ∞ (raw M hM) :=
  CompactLift.velocity_smooth verticalCutoff_smooth
    (compactVelocity_smooth (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM))

theorem velocity_smooth (M : Alternating.Machine) (hM : M.WellFormed) :
    ContDiff ℝ ∞ (velocity M hM) := BalancedStretch.velocity_smooth (raw_smooth M hM)

theorem raw_support (M : Alternating.Machine) (hM : M.WellFormed) (t : ℝ) :
    tsupport (fun x => raw M hM (t, x)) ⊆ rawSupport := by
  apply closure_minimal _ rawSupport_compact.isClosed
  intro x hx
  have hχ : verticalCutoff (x 2) ≠ 0 := by
    intro hz
    apply hx
    simp only [raw, CompactLift.velocity, CompactLift.spatial, hz, zero_smul]
  have hV : BalancedPlanar.bodyVelocity M hM t (horizontal x) ≠ 0 := by
    intro hz
    apply hx
    simp only [raw, CompactLift.velocity, CompactLift.spatial, VelocityDetector.triangularLift,
      VelocityDetector.horizontalLinear_eq, hz, map_zero, zero_smul, add_zero, smul_zero]
  have hp := commonSupport_in_unit
    (normalizedPulse_inUnit (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM))
    (compactVelocity_support (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM)
      t (subset_tsupport _ hV))
  have hz := closedCutoff_support (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (1 : ℝ) < 2) hχ
  constructor <;> intro j <;> fin_cases j
  · exact (hp 0).1.le
  · exact (hp 1).1.le
  · exact hz.1.le
  · exact (hp 0).2.le
  · exact (hp 1).2.le
  · exact hz.2.le

theorem velocity_support (M : Alternating.Machine) (hM : M.WellFormed) (t : ℝ) :
    tsupport (fun x => velocity M hM (t, x)) ⊆ support := by
  change tsupport (BalancedStretch.push (fun x => raw M hM (t,x))) ⊆
    BalancedStretch.stretch '' rawSupport
  exact BalancedStretch.push_support (a := fun x => raw M hM (t,x))
    (K := rawSupport) rawSupport_compact.isClosed (raw_support M hM t)

theorem raw_divergence (M : Alternating.Machine) (hM : M.WellFormed) (t : ℝ) (x : Space) :
    divergence (fun y => raw M hM (t, y)) x = 0 := by
  have hs := field_smooth (periodicHamiltonian_slice_smooth
    (normalizedPulse (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM)) t)
  change ContDiff ℝ ∞ (BalancedPlanar.bodyVelocity M hM t) at hs
  rw [show (fun y => raw M hM (t, y)) =
    CompactLift.spatial verticalCutoff (BalancedPlanar.bodyVelocity M hM t) from rfl,
    CompactLift.spatial_divergence verticalCutoff_smooth hs]
  have hz : PlanarHamiltonian.divergence (BalancedPlanar.bodyVelocity M hM t)
      (horizontal x) = 0 :=
    (periodicVelocity_properties
      (normalizedPulse_valid (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM)) t).2.1 _
  rw [hz, mul_zero]

theorem velocity_divergence (M : Alternating.Machine) (hM : M.WellFormed) :
    Solenoidal (velocity M hM) :=
  BalancedStretch.velocity_divergence (raw_divergence M hM)

theorem raw_periodic (M : Alternating.Machine) (hM : M.WellFormed) :
    TimePeriodic (raw M hM) := by
  intro t x
  have he : BalancedPlanar.bodyVelocity M hM (t + 1) = BalancedPlanar.bodyVelocity M hM t :=
    funext (fun y => periodicVelocity_periodic _ y t)
  simp only [raw, CompactLift.velocity, he]

theorem velocity_periodic (M : Alternating.Machine) (hM : M.WellFormed) :
    TimePeriodic (velocity M hM) := by
  intro t x
  change BalancedStretch.stretch (raw M hM (t + 1, BalancedStretch.stretch.symm x)) =
    BalancedStretch.stretch (raw M hM (t, BalancedStretch.stretch.symm x))
  rw [raw_periodic M hM]

theorem velocity_bounded (M : Alternating.Machine) (hM : M.WellFormed) :
    BoundedMixedDerivatives (velocity M hM) :=
  boundedMixed_of_compact_periodic (velocity_smooth M hM) support_compact
    (velocity_support M hM) (velocity_periodic M hM)

end ForcedComputation.BalancedBody

end

end OAI
