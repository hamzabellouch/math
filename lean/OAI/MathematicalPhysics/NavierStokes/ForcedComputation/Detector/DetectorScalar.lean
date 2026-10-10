import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorStirring
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarZeroExtension

namespace OAI

/-! The explicit detector source and drift have one global smooth,
nonnegative scalar evolution, conditional only on the published existence
input. The drift and source never depend on this unknown scalar. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem detectorScalar_exists (hE : TorusScalarExistence)
    {V : ℝ → Plane → Plane} (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hVp : ∀ t, PlanePeriodic (V t)) (C L : ℕ) :
    ∃ w : ℝ → Plane → ℝ,
      GlobalTorusScalarSolution 1 (detectorDrift V C L) (detectorSource C L) w (fun _ => 0) ∧
      ContDiff ℝ ∞ (Function.uncurry w) ∧
      (∀ t, PlanePeriodic (w t)) ∧
      (∀ t x, 0 ≤ w t x) ∧
      (∀ t, t ≤ 1 → ∀ x, w t x = 0) := by
  obtain ⟨w, hw⟩ := hE.global 1 (by norm_num) (detectorDrift V C L)
    (detectorSource C L) (fun _ => 0) (detectorDrift_smooth hV C L)
    (detectorSource_smooth C L) contDiff_const (detectorDrift_periodic hVp C L)
    (detectorSource_periodic C L) (fun _ _ => rfl)
  have hsol := hw.zeroExtension
  have hzero (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : Plane) :
      detectorSource C L t x = 0 := detectorSource_before_one C L ht.2 x
  have hnonneg := hsol.nonnegative (by norm_num : (0 : ℝ) ≤ 1)
    (fun t _ x => detectorSource_nonnegative C L t x) (fun _ => le_rfl)
  refine ⟨scalarZeroExtension w, hsol,
    hw.zeroExtension_smooth (by norm_num) hzero, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : 0 ≤ t
    · exact (hsol t ht).periodic t ⟨ht, le_rfl⟩
    · intro x k
      simp only [scalarZeroExtension, ite_eq_right ht]
  · intro t x
    by_cases ht : 0 ≤ t
    · exact hnonneg t ht x
    · simp only [scalarZeroExtension, ite_eq_right ht, le_refl]
  · intro t ht x
    by_cases ht₀ : 0 ≤ t
    · simp only [scalarZeroExtension, ite_eq_left ht₀]
      exact hw.zero_before_one (by norm_num) hzero t ⟨ht₀, ht⟩ x
    · simp only [scalarZeroExtension, ite_eq_right ht₀]

end ForcedComputation.VelocityDetector

end

end OAI
