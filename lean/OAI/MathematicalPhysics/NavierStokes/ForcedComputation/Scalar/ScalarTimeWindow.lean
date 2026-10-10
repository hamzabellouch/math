import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatEvolution

namespace OAI

/-! Restriction to a physical time window, and the exact heat evolution
during an interval on which the prescribed drift and source vanish. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem GlobalTorusScalarSolution.window {ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hs : GlobalTorusScalarSolution ν a h w w₀)
    (hw : ContDiff ℝ ∞ (Function.uncurry w))
    {s T : ℝ} (hs₀ : 0 ≤ s) (_hT : 0 ≤ T) :
    TorusScalarSolution T ν (fun t => a (s + t)) (fun t => h (s + t))
      (fun t => w (s + t)) (w s) := by
  refine ⟨(hw.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)).contDiffOn,
    ?_, ?_, ?_⟩
  · intro t ht
    have ht₀ : 0 ≤ s + t := add_nonneg hs₀ ht.1
    exact (hs (s + t) ht₀).periodic (s + t) ⟨ht₀, le_rfl⟩
  · simp only [add_zero]
  · intro t ht x
    have hd : HasDerivAt (fun r => w r x)
        (scalarGenerator ν (a (s + t)) (w (s + t)) x + h (s + t) x) (s + t) := by
      rw [← hs.deriv_eq hw (add_nonneg hs₀ ht.1) x]
      exact ((hw.comp (contDiff_id.prodMk contDiff_const)).differentiable
        (by simp) (s + t)).hasDerivAt
    simpa only [mul_one, Function.comp_def, id_eq] using
      (hd.comp t ((hasDerivAt_id t).const_add s)).hasDerivWithinAt

theorem GlobalTorusScalarSolution.heat_window (hK : TorusHeatInput)
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hs : GlobalTorusScalarSolution 1 a h w w₀)
    (hw : ContDiff ℝ ∞ (Function.uncurry w))
    {s T : ℝ} (hs₀ : 0 ≤ s) (hT : 0 ≤ T)
    (ha : ∀ t ∈ Icc (0 : ℝ) T, a (s + t) = fun _ => 0)
    (hh : ∀ t ∈ Icc (0 : ℝ) T, h (s + t) = fun _ => 0) :
    ∀ t ∈ Icc (0 : ℝ) T, w (s + t) = torusHeatEvolution (w s) t := by
  have hwin := hs.window hw hs₀ hT
  have hzero : TorusScalarSolution T 1 (fun _ _ => 0) (fun _ _ => 0)
      (fun t => w (s + t)) (w s) := by
    refine { hwin with equation := ?_ }
    intro t ht x
    simpa only [ha t ht, hh t ht] using hwin.equation t ht x
  have hp : PlanePeriodic (w s) := (hs s hs₀).periodic s ⟨hs₀, le_rfl⟩
  exact hzero.unique
    (hK.solution T hT (w s) (hw.comp (contDiff_const.prodMk contDiff_id)) hp)
    hT (by norm_num)

end ForcedComputation.VelocityDetector

end

end OAI
