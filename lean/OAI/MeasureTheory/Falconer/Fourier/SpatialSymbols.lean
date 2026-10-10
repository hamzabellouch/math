import OAI.MeasureTheory.Falconer.Fourier.BorelSymbols
import OAI.MeasureTheory.Falconer.Fourier.AllDimensionalSpatialFourierIntegration

namespace OAI

/-! # Spatial Fourier factors preserve angular symbol control -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem ChartSymbolControl.spatialMultiplier {n m : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D : ℝ}
    (h : ChartSymbolControl m b B D)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1) :
    ChartSymbolControl m (fun x w => c x*b x w) B D := by
  refine ⟨(hc.comp measurable_fst).mul h.measurable,?_,?_,?_⟩
  · intro x w
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hcb x) (norm_nonneg _)).trans
      (by simpa only [one_mul] using h.bound x w)
  · intro x e y
    have he : rotatedChartAmplitude e (fun w => c x*b x w) y =
        fun u => c x*rotatedChartAmplitude e (b x) y u := rfl
    rw [he]
    exact contDiff_const.mul (h.smooth x e y)
  · intro e k hk x y hy u hu
    have he : rotatedChartAmplitude e (fun w => c x*b x w) y =
        fun u => c x*rotatedChartAmplitude e (b x) y u := rfl
    rw [he,iteratedDeriv_const_mul (c x) ((h.smooth x e y).of_le (by simp)).contDiffAt,
      norm_mul]
    exact (mul_le_mul_of_nonneg_right (hcb x) (norm_nonneg _)).trans
      (by simpa only [one_mul] using h.derivative e k hk x y hy u hu)

theorem ChartSymbolControl.spatialFourier {n m : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D : ℝ}
    (h : ChartSymbolControl m b B D) (s : ℝ) (ξ : Space (n+2)) :
    ChartSymbolControl m (fun x w => spatialFourierPhase s ξ x*b x w) B D :=
  h.spatialMultiplier _ (by unfold spatialFourierPhase; fun_prop)
    (fun x => (spatialFourierPhase_norm s ξ x).le)

end Falconer

end OAI
