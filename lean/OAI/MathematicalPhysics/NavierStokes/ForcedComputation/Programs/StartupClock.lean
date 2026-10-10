import Mathlib
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.Reparametrization

namespace OAI

/-!
# A startup ramp has an onto accumulated clock

This supplies the time-change argument in the eventually stationary forcing
construction. Nonnegativity controls the initial interval; the constant tail
ensures that every finite computational time is reached.
-/

noncomputable section

open Set
open scoped ContDiff

namespace ForcedComputation

def accumulatedClock (α : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in 0..t, α s

theorem accumulatedClock_zero (α : ℝ → ℝ) : accumulatedClock α 0 = 0 := by
  simp [accumulatedClock]

theorem accumulatedClock_hasDerivAt {α : ℝ → ℝ} (hα : Continuous α) (t : ℝ) :
    HasDerivAt (accumulatedClock α) (α t) t :=
  intervalIntegral.integral_hasDerivAt_right (hα.intervalIntegrable _ _)
    hα.aestronglyMeasurable.stronglyMeasurableAtFilter hα.continuousAt

theorem accumulatedClock_nonneg {α : ℝ → ℝ}
    (hα : ∀ t, 0 ≤ t → 0 ≤ α t) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ accumulatedClock α t :=
  intervalIntegral.integral_nonneg ht (fun s hs => hα s hs.1)

theorem accumulatedClock_tail {α : ℝ → ℝ} (hα : Continuous α)
    (htail : ∀ t, 1 ≤ t → α t = 1) {t : ℝ} (ht : 1 ≤ t) :
    accumulatedClock α t = accumulatedClock α 1 + (t - 1) := by
  unfold accumulatedClock
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hα.intervalIntegrable 0 1) (hα.intervalIntegrable 1 t)]
  congr 1
  calc
    (∫ s in (1 : ℝ)..t, α s) = ∫ _s in (1 : ℝ)..t, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht] at hs
      exact htail s hs.1
    _ = t - 1 := by simp

theorem accumulatedClock_onto {α : ℝ → ℝ} (hα : Continuous α)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) (htail : ∀ t, 1 ≤ t → α t = 1) :
    OntoClock (accumulatedClock α) := by
  refine ⟨fun _ ht => accumulatedClock_nonneg hnonneg ht, ?_⟩
  intro s hs
  have hc : Continuous (accumulatedClock α) :=
    (show Differentiable ℝ (accumulatedClock α) from
      fun t => (accumulatedClock_hasDerivAt hα t).differentiableAt).continuous
  have hb : s ≤ accumulatedClock α (s + 1) := by
    rw [accumulatedClock_tail hα htail (by linarith)]
    have hzero := accumulatedClock_nonneg hnonneg (show (0 : ℝ) ≤ 1 by norm_num)
    linarith
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ s + 1 by linarith)
    hc.continuousOn (show s ∈ Icc (accumulatedClock α 0)
      (accumulatedClock α (s + 1)) by rw [accumulatedClock_zero]; exact ⟨hs, hb⟩)
  exact ⟨t, ht.1, he⟩

/-- A completely specified fixed startup, zero until time `1/2` and one from time `1`. -/
def startupRamp (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

theorem startupRamp_smooth : ContDiff ℝ ∞ startupRamp := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem startupRamp_zero : startupRamp 0 = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  norm_num

theorem startupRamp_nonneg (t : ℝ) : 0 ≤ startupRamp t :=
  Real.smoothTransition.nonneg _

theorem startupRamp_tail {t : ℝ} (ht : 1 ≤ t) : startupRamp t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem startupClock_onto : OntoClock (accumulatedClock startupRamp) :=
  accumulatedClock_onto startupRamp_smooth.continuous
    (fun t _ => startupRamp_nonneg t) (fun _ ht => startupRamp_tail ht)

end ForcedComputation

end

end OAI
