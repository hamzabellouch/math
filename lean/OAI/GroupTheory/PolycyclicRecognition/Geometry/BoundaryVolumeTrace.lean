import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryCompactSandwich
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryHeight
import Mathlib.MeasureTheory.Measure.Haar.Basic

namespace OAI

/-! # Boundary volume sandwiches bound trace-height differences -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

/-- Equal source boundary sets have equal images. A fixed positive lower
volume and finite upper volume then bound the difference of the two
logarithmic Haar characters. The constant is independent of the map. -/
theorem boundary_trace_bound_of_sandwich
    {P G S T : Type*} [Group G] [MeasurableSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T)
    (B : P → S → T) (f : P → G → G) (μ : Measure T) (height : G → ℝ)
    (hvolume : ∀ g E, μ (actT g '' E) = ENNReal.ofReal (Real.exp (height g)) * μ E)
    (U : Set S) (Vminus Vplus : Set T)
    (hVminus0 : μ Vminus ≠ 0) (hVminusfinite : μ Vminus ≠ ⊤) (hVplusfinite : μ Vplus ≠ ⊤)
    (hsandwich : ∀ p x, actT (f p x) '' Vminus ⊆ B p '' (actS x '' U) ∧
      B p '' (actS x '' U) ⊆ actT (f p x) '' Vplus) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p x y, actS x '' U = actS y '' U →
      |height (f p x) - height (f p y)| ≤ K := by
  let c := (μ Vminus).toReal
  let C := (μ Vplus).toReal
  have hc : 0 < c := ENNReal.toReal_pos hVminus0 hVminusfinite
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  let K := C / c + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKc : K * c = C + c := by
    dsimp only [K]
    rw [add_mul, div_mul_cancel₀ _ hc.ne', one_mul]
  have hcmp (p : P) (x y : G) (he : actS x '' U = actS y '' U) :
      Real.exp (height (f p x)) ≤ K * Real.exp (height (f p y)) := by
    have hs : actT (f p x) '' Vminus ⊆ actT (f p y) '' Vplus := by
      exact (hsandwich p x).1.trans (he ▸ (hsandwich p y).2)
    have hm := measure_mono (μ := μ) hs
    rw [hvolume, hvolume] at hm
    have hr := ENNReal.toReal_mono (by finiteness) hm
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hr
    change Real.exp (height (f p x)) * c ≤ Real.exp (height (f p y)) * C at hr
    have hh : Real.exp (height (f p x)) * c ≤ (K * Real.exp (height (f p y))) * c := by
      calc
        Real.exp (height (f p x)) * c ≤ Real.exp (height (f p y)) * C := hr
        _ ≤ Real.exp (height (f p y)) * (C + c) := by gcongr; linarith
        _ = (K * Real.exp (height (f p y))) * c := by rw [mul_assoc, mul_comm (Real.exp _) c, ← mul_assoc, hKc, mul_comm]
    exact (mul_le_mul_iff_left₀ hc).mp hh
  refine ⟨max 0 (Real.log K), le_max_left _ _, ?_⟩
  intro p x y he
  exact (abs_sub_le_log_of_exp_comparison hK (hcmp p x y he) (hcmp p y x he.symm)).trans
    (le_max_right _ _)

end PolycyclicRecognition

end

end OAI
