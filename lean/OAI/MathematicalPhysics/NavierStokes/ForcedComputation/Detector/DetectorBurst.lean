import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorReferenceBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorSchedule
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarTimeWindow
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarBurstError

namespace OAI

/-! The prescribed burst is compared directly with its inviscid reference.
Previously injected scalar enters only through its bound at the start. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem detectorReference_periodic {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hp : ∀ s, PlanePeriodic (V s)) (C L n : ℕ) (t : ℝ) :
    PlanePeriodic (detectorReference Ψ C L n t) := by
  intro x k
  unfold detectorReference
  rw [pullbackScalar_periodic hΨ hp (detectorBump_periodic _) _ x k]

theorem detectorReference_initial (Ψ : ℝ → ℝ → Plane → Plane) (C L n : ℕ) (x : Plane) :
    detectorReference Ψ C L n (2 * ((n : ℝ) + 1)) x = 0 := by
  simp only [detectorReference, detectorInjectionFraction, sub_self, zero_div]
  rw [smoothRamp_before (by norm_num : (0 : ℝ) < 1) le_rfl, zero_mul]

theorem detectorReference_solution {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hp : ∀ s, PlanePeriodic (V s))
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2)) (C L n : ℕ) :
    TorusScalarSolution (2 * (duration C L n : ℝ)) 1
      (fun t => detectorDrift V C L (2 * ((n : ℝ) + 1) + t))
      (fun t x => detectorSource C L (2 * ((n : ℝ) + 1) + t) x -
        scalarLaplacian (detectorReference Ψ C L n (2 * ((n : ℝ) + 1) + t)) x)
      (fun t => detectorReference Ψ C L n (2 * ((n : ℝ) + 1) + t)) (fun _ => 0) := by
  let S := 2 * ((n : ℝ) + 1)
  refine ⟨((detectorReference_smooth hback C L n).comp
    ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)).contDiffOn, ?_, ?_, ?_⟩
  · intro t _
    exact detectorReference_periodic hΨ hp C L n _
  · funext x
    simpa only [add_zero] using detectorReference_initial Ψ C L n x
  · intro t ht x
    have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
    have hδ := detector_duration_real_le C L n
    have hi : S + t ∈ Icc (2 * ((n : ℝ) + 1)) (2 * ((n : ℝ) + 2)) := by
      dsimp only [S]
      constructor <;> linarith [ht.1, ht.2]
    have he := (detectorReference_equation hΨ hback C L n (S + t) x).comp t
      ((hasDerivAt_id t).const_add S)
    rw [← detectorDrift_eq_term V C L n hi x, ← detectorSource_eq_term C L n hi x] at he
    convert he.hasDerivWithinAt (s := Icc (0 : ℝ) (2 * (duration C L n : ℝ))) using 1
    · rfl
    · simp only [scalarGenerator, one_mul, mul_one]
      ring

theorem detectorBurst_comparison {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hp : ∀ s, PlanePeriodic (V s))
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (C L n : ℕ) {w : ℝ → Plane → ℝ}
    (hs : GlobalTorusScalarSolution 1 (detectorDrift V C L) (detectorSource C L)
      w (fun _ => 0)) (hw : ContDiff ℝ ∞ (Function.uncurry w))
    (hlap : ∀ t ∈ Icc (0 : ℝ) (2 * (duration C L n : ℝ)), ∀ x,
      |scalarLaplacian (detectorReference Ψ C L n (2 * ((n : ℝ) + 1) + t)) x| ≤
        (laplacianBound C L n : ℝ))
    {E : ℝ} (hinit : ∀ x, |w (2 * ((n : ℝ) + 1)) x| ≤ E) :
    ∀ t ∈ Icc (0 : ℝ) (2 * (duration C L n : ℝ)), ∀ x,
      |w (2 * ((n : ℝ) + 1) + t) x -
        detectorReference Ψ C L n (2 * ((n : ℝ) + 1) + t) x| < E + 1 / 16 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  exact scalar_burst_error_initial C L n
    (hs.window hw (by positivity) (by positivity))
    (detectorReference_solution hΨ hp hback C L n) hlap
    (fun x => by simpa only [sub_zero] using hinit x)

end ForcedComputation.VelocityDetector

end

end OAI
