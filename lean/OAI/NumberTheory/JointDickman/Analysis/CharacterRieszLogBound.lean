import OAI.NumberTheory.JointDickman.Analysis.CharacterPerronLogBound

namespace OAI

/-! # Uniform logarithmic cancellation in the actual character Riesz sum -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem squarefreeCharacterRiesz_log_bound {z C D : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q:ℝ) ≤ (Real.log x)^C → χ ≠ 1 →
        ‖squarefreeCharacterRieszSum χ z x‖ ≤ K*x*(Real.log x)^(-D) := by
  obtain ⟨K,hK,h⟩ := characterPerron_log_bound hz hz1 hC hD
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually h] with x hx hh
  intro q _ χ hq hn
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hp := hh q χ hq hn
  have he := characterNormalizedPerron_riesz χ (L := Real.log x) hz hz1
    (one_div_pos.mpr hl)
  rw [Real.exp_log hx0] at he
  rw [←he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  calc
    _ ≤ x*(K*(Real.log x)^(-D)) := mul_le_mul_of_nonneg_left hp hx0.le
    _ = _ := by ring

end JointDickman

end OAI
