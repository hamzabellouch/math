import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorBurst

namespace OAI

/-! Each smooth stirring clock visits every phase of its finite prefix.
The characteristic carrying the bump center then gives a velocity above
the fixed detection threshold. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem detectorPhase_hits (C L n : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (hsn : s ≤ (n : ℝ) + 1) :
    ∃ t ∈ Icc (2 * ((n : ℝ) + 1) + (duration C L n : ℝ))
      (2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ)), detectorPhase C L n t = s := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  apply intermediate_value_Icc (by linarith)
    (detectorPhase_smooth C L n).continuous.continuousOn
  rw [detectorPhase_before C L n le_rfl, detectorPhase_after C L n le_rfl]
  exact ⟨hs, hsn⟩

theorem detectorBurst_detects {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hp : ∀ s, PlanePeriodic (V s))
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (C L n : ℕ) {w : ℝ → Plane → ℝ}
    (hwsol : GlobalTorusScalarSolution 1 (detectorDrift V C L) (detectorSource C L)
      w (fun _ => 0)) (hw : ContDiff ℝ ∞ (Function.uncurry w))
    (hlap : ∀ t ∈ Icc (0 : ℝ) (2 * (duration C L n : ℝ)), ∀ x,
      |scalarLaplacian (detectorReference Ψ C L n (2 * ((n : ℝ) + 1) + t)) x| ≤
        (laplacianBound C L n : ℝ))
    {E : ℝ} (hE : E ≤ 1 / 16)
    (hinit : ∀ x, |w (2 * ((n : ℝ) + 1)) x| ≤ E)
    {s : ℝ} (hs : 0 ≤ s) (hsn : s ≤ (n : ℝ) + 1) :
    ∃ t, 0 ≤ t ∧ 1 / 2 < w t (Ψ 0 s ![1 / 4, 1 / 4]) := by
  obtain ⟨t, ht, he⟩ := detectorPhase_hits C L n hs hsn
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  let S := 2 * ((n : ℝ) + 1)
  have hτ : t - S ∈ Icc (0 : ℝ) (2 * (duration C L n : ℝ)) := by
    dsimp only [S]
    constructor <;> linarith [ht.1, ht.2]
  have herror := detectorBurst_comparison hΨ hp hback C L n hwsol hw hlap hinit
    (t - S) hτ (Ψ 0 s ![1 / 4, 1 / 4])
  have hcancel : 2 * ((n : ℝ) + 1) + (t - S) = t := by dsimp only [S]; ring
  rw [hcancel] at herror
  have href := detectorReference_at_characteristic hΨ C L n ht.1
  rw [he] at href
  rw [href] at herror
  refine ⟨t, ?_, ?_⟩
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [ht.1]
  · have hh := (abs_lt.mp herror).1
    linarith

end ForcedComputation.VelocityDetector

end

end OAI
