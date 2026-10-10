import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SpatialSuspension
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ExpressionCompiler

namespace OAI

/-! The fixed, mean-zero spatial clock. It runs at unit speed throughout the
planar computational corridor and is a finite periodic cutoff expression. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set MeasureTheory
open scoped ContDiff

def clockRectangle : RationalBox 2 :=
  ⟨![1 / 8, 1 / 32], ![7 / 8, 7 / 8]⟩

def unitSpatialClock : Plane → ℝ := planarMask 1 clockRectangle (1 / 128)

theorem unitSpatialClock_smooth : ContDiff ℝ ∞ unitSpatialClock :=
  planarMask_smooth (by norm_num) _ (by norm_num)

theorem unitSpatialClock_periodic (x : Plane) (n : Fin 2 → ℤ) :
    unitSpatialClock (x + fun j => (n j : ℝ)) = unitSpatialClock x := by
  simpa only [unitSpatialClock, one_mul] using planarMask_periodic 1 clockRectangle (1 / 128) x n

theorem unitSpatialClock_one {x : Plane} (hx : x ∈ clockRectangle.carrier) :
    unitSpatialClock x = 1 := by
  apply planarMask_plateau (A := fun _ => 0) (B := fun _ => 1) (by norm_num)
    (by intro j; norm_num) clockRectangle (by norm_num)
  · intro j
    fin_cases j <;> norm_num [clockRectangle]
  · have hr : (0 : ℝ) < (1 / 128 : ℚ) := by norm_num
    intro j
    exact ⟨by linarith [(hx j).1], by linarith [(hx j).2]⟩

def verticalClock (x : Space) : Space :=
  letI := ShearFlows.neZeroThree
  unitSpatialClock (horizontal x) • basis 2

theorem verticalClock_smooth : ContDiff ℝ ∞ verticalClock := by
  have he : verticalClock = fun x => unitSpatialClock (selectTwo 0 1 x) • basis 2 := by
    funext x
    rw [selectTwo_zero_one]
    rfl
  rw [he]
  exact (unitSpatialClock_smooth.comp (selectTwo 0 1).contDiff).smul contDiff_const

theorem verticalClock_divergence (x : Space) : divergence verticalClock x = 0 := by
  have he : verticalClock = transverseSum (ι := Unit) (selectTwo 0 1)
      (fun _ => unitSpatialClock) (fun _ => basis 2) := by
    funext y
    simp only [verticalClock, transverseSum, Finset.univ_unique,
      Finset.sum_singleton, selectTwo_zero_one]
  rw [he]
  exact transverseSum_divergence _ _ _
    (fun _ => selectTwo_basis (by decide) (by decide)) x
    (fun _ => unitSpatialClock_smooth.differentiable (by simp) _)

theorem verticalClock_mean_zero : (∫ x in fundamentalCube 1, verticalClock x) = 0 := by
  change (∫ x in fundamentalCube 1, unitSpatialClock (horizontal x) • basis 2) = 0
  rw [integral_smul_const]
  have hz : (∫ x in fundamentalCube 1, unitSpatialClock (horizontal x)) = 0 :=
    planarMask_cube_mean_zero (by norm_num) _ (by norm_num)
  rw [hz, zero_smul]

def unitSpatialClockExpr : FieldExpr := FieldExpr.planeMask 1 clockRectangle (1 / 128)

theorem unitSpatialClockExpr_valid : unitSpatialClockExpr.Valid :=
  FieldExpr.planeMask_valid (by norm_num) (by norm_num) _

theorem unitSpatialClockExpr_val (y : SpaceTime) :
    unitSpatialClockExpr.val y = unitSpatialClock (horizontal y.2) := by
  simpa only [unitSpatialClockExpr, unitSpatialClock, Rat.cast_one] using
    FieldExpr.planeMask_val (L := 1) (r := 1 / 128) (by norm_num) (by norm_num) clockRectangle y

end ForcedComputation

end

end OAI
