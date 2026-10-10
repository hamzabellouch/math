import OAI.NumberTheory.DirichletL.Descent.WindowFourier

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem inverseNormWindow_contDiff (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (inverseNormWindow V) := by
  unfold inverseNormWindow
  have hn : ∀ y : ℝ, (Real.exp y : ℂ) ≠ 0 := by
    intro y
    exact_mod_cast Real.exp_ne_zero y
  simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using
    hV.mul ((Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).inv hn)

theorem inverseRootWindow_contDiff (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (inverseRootWindow V) := by
  unfold inverseRootWindow
  have hs : ContDiff ℝ ∞ (fun y : ℝ => Real.sqrt (Real.exp y)) :=
    Real.contDiff_exp.sqrt Real.exp_ne_zero
  have hn : ∀ y : ℝ, (Real.sqrt (Real.exp y) : ℂ) ≠ 0 := by
    intro y
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (Real.exp_pos y))
  simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using
    hV.mul ((Complex.ofRealCLM.contDiff.comp hs).inv hn)

theorem inverseNormWindow_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (inverseNormWindow V) := by
  apply hV.mono
  intro y hy
  exact (div_ne_zero_iff.mp hy).1

theorem inverseRootWindow_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (inverseRootWindow V) := by
  apply hV.mono
  intro y hy
  exact (div_ne_zero_iff.mp hy).1

theorem firstRootWindows_smooth_compact (V : Fin 9 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    ∀ i, ContDiff ℝ ∞ (firstRootWindows V i) ∧ HasCompactSupport (firstRootWindows V i) := by
  intro i
  fin_cases i <;> first
    | exact ⟨hV _, hS _⟩
    | exact ⟨inverseNormWindow_contDiff _ (hV _), inverseNormWindow_compact _ (hS _)⟩
    | exact ⟨inverseRootWindow_contDiff _ (hV _), inverseRootWindow_compact _ (hS _)⟩

theorem secondRootWindows_smooth_compact (V : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    ∀ i, ContDiff ℝ ∞ (secondRootWindows V i) ∧ HasCompactSupport (secondRootWindows V i) := by
  intro i
  fin_cases i <;> first
    | exact ⟨hV _, hS _⟩
    | exact ⟨inverseNormWindow_contDiff _ (hV _), inverseNormWindow_compact _ (hS _)⟩
    | exact ⟨inverseRootWindow_contDiff _ (hV _), inverseRootWindow_compact _ (hS _)⟩

end
end SevenEighths.InverseMoment

end OAI
