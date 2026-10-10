import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingCutoffTransport
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateCollars

namespace OAI

/-! Each individual gate carries a uniformly compact family of tests,
including the time derivative, over its whole scheduled motion. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set
open scoped ContDiff

theorem scheduledCenter_bounded (a : ℝ) {T : ℝ} (hT : 0 < T)
    (S S' : ℝ) (k target : ℕ) (terminal : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, ‖scheduledCenter a T S S' k target terminal t‖ ≤ B := by
  let c := scheduledCenter a T S S' k target terminal
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    ((scheduledCenter_smooth a T S S' k target terminal).continuous.norm.continuousOn :
      ContinuousOn (fun t => ‖c t‖) (Icc a (a + T)))
  have hb (t : ℝ) (ht : t ∈ Icc a (a + T)) : ‖c t‖ ≤ B :=
    hB (mem_image_of_mem _ ht)
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro t
  change ‖c t‖ ≤ max 0 B
  by_cases hleft : t < a
  · have he : c t = c a := by
      rw [show c t = ![S * k, -S] from scheduledCenter_before a hT S S' k target terminal (by linarith),
        show c a = ![S * k, -S] from scheduledCenter_initial a hT S S' k target terminal]
    rw [he]
    exact (hb a ⟨le_rfl, by linarith⟩).trans (le_max_right _ _)
  · by_cases hright : a + T < t
    · have he : c t = c (a + T) := by
        rw [show c t = ![S' * target, if terminal then S' else -S'] from
            scheduledCenter_after a hT S S' k target terminal (by linarith),
          show c (a + T) = ![S' * target, if terminal then S' else -S'] from
            scheduledCenter_final a hT S S' k target terminal]
      rw [he]
      exact (hb (a + T) ⟨by linarith, le_rfl⟩).trans (le_max_right _ _)
    · exact (hb t ⟨le_of_not_gt hleft, le_of_not_gt hright⟩).trans (le_max_right _ _)

theorem concentrationFamily_compact {R : ℝ} (hR : 0 < R)
    {c : ℝ → Plane} {B : ℝ} (hB : ∀ t, ‖c t‖ ≤ B) :
    ∃ K : Set Plane, IsCompact K ∧
      (∀ t, Function.support (concentrationCutoff R (c t)) ⊆ K) ∧
      (∀ t, Function.support (concentrationDerivative R c t) ⊆ K) := by
  let K : Set Plane := Icc (fun _ => -B - R) (fun _ => B + R)
  have hb (t : ℝ) (x : Plane) (hx : ∀ j, |x j - c t j| ≤ R) : x ∈ K := by
    constructor <;> intro j
    · have hc : |c t j| ≤ B :=
        (show |c t j| ≤ ‖c t‖ from by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (c t) j).trans (hB t)
      have hj := (abs_le.mp (hx j)).1
      have hjc := (abs_le.mp hc).1
      dsimp [K]
      linarith
    · have hc : |c t j| ≤ B :=
        (show |c t j| ≤ ‖c t‖ from by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (c t) j).trans (hB t)
      have hj := (abs_le.mp (hx j)).2
      have hjc := (abs_le.mp hc).2
      dsimp [K]
      linarith
  refine ⟨K, isCompact_Icc, ?_, ?_⟩
  · exact fun t x hx => hb t x (concentrationCutoff_support hR (c t) hx)
  · exact fun t x hx => hb t x (concentrationDerivative_support hR c t hx)

end ForcedComputation.ExpandingDetector

end

end OAI
