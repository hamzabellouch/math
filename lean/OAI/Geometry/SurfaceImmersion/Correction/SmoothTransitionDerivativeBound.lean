import OAI.Geometry.SurfaceImmersion.Atlas.IntervalInteriorCutoff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! A fixed bound for the derivative of the standard smooth step. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem smoothTransition_derivative_bound : ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C := by
  have hψ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd : ContDiff ℝ ∞ (deriv Real.smoothTransition) := hψ.deriv'
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    hd.continuous.continuousOn
  refine ⟨|B|+1,by positivity,?_⟩
  intro x
  by_cases hx : x ∈ Icc (0:ℝ) 1
  · have hb' : |deriv Real.smoothTransition x| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB x hx
    exact hb'.trans (by linarith [le_abs_self B])
  · have hz : deriv Real.smoothTransition x = 0 := by
      rcases lt_or_ge x 0 with hl | hl
      · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
          filter_upwards [isOpen_Iio.mem_nhds hl] with y hy
          exact Real.smoothTransition.zero_of_nonpos hy.le
        rw [he.deriv_eq]
        exact deriv_const _ _
      · have hr : 1 < x := lt_of_not_ge (fun h => hx ⟨hl,h⟩)
        have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hr] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le
        rw [he.deriv_eq]
        exact deriv_const _ _
    rw [hz,abs_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
