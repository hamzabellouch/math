import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact

namespace OAI

namespace SiegelZeros

section

noncomputable section
open Complex Set Filter
open scoped Topology
namespace Awei.W53

def zetaPoleRemoved (s : ℂ) : ℂ :=
  ((s - 1) * (completedRiemannZeta₀ s - 1 / s) + 1) * (Gammaℝ s)⁻¹

@[simp] theorem zetaPoleRemoved_one : zetaPoleRemoved 1 = 1 := by
  simp [zetaPoleRemoved]

theorem analyticAt_zetaPoleRemoved {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ zetaPoleRemoved s := by
  exact (((analyticAt_id.sub analyticAt_const).mul
    ((differentiable_completedZeta₀.analyticAt s).sub
      (analyticAt_const.div analyticAt_id hs))).add analyticAt_const).mul
        (differentiable_Gammaℝ_inv.analyticAt s)

theorem zetaPoleRemoved_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    zetaPoleRemoved s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
  unfold zetaPoleRemoved
  have h1 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  simp only [div_eq_mul_inv]
  rw [← mul_assoc]
  congr 1
  field_simp
  ring

theorem deriv_zetaPoleRemoved {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv zetaPoleRemoved s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have heq : zetaPoleRemoved =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
    exact zetaPoleRemoved_eq hz0 hz1
  rw [heq.deriv_eq]
  simpa [Pi.mul_def] using (((hasDerivAt_id s).sub_const 1).mul
    (differentiableAt_riemannZeta hs1).hasDerivAt).deriv

theorem zeta_logDerivative_identity {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s - 1 / (s - 1) =
      -deriv zetaPoleRemoved s / zetaPoleRemoved s := by
  rw [deriv_zetaPoleRemoved hs0 hs1, zetaPoleRemoved_eq hs0 hs1]
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

theorem zetaPoleRemoved_ne_zero_real {s : ℝ} (hs : 1 ≤ s) :
    zetaPoleRemoved (s : ℂ) ≠ 0 := by
  rcases eq_or_lt_of_le hs with h | h
  · subst s
    simp
  · have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by linarith)
    have hs1 : (s : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt h)
    rw [zetaPoleRemoved_eq hs0 hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_lt_re h)

theorem zeta_logDerivative_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1)‖ ≤ C := by
  let f : ℝ → ℝ := fun s => ‖-deriv zetaPoleRemoved (s : ℂ) / zetaPoleRemoved (s : ℂ)‖
  have hc : ContinuousOn f (Icc 1 2) := by
    intro s hs
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by linarith [hs.1])
    have ha := analyticAt_zetaPoleRemoved hs0
    exact (((ha.deriv.continuousAt.neg.div ha.continuousAt
      (zetaPoleRemoved_ne_zero_real hs.1)).comp continuous_ofReal.continuousAt).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro s hs hs2
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by linarith)
  have hs1 : (s : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hs)
  rw [zeta_logDerivative_identity hs0 hs1 (riemannZeta_ne_zero_of_one_lt_re hs)]
  exact (hB (mem_image_of_mem f ⟨hs.le, hs2⟩)).trans (le_max_left _ _)

theorem zeta_logDerivative_re_upper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re ≤ C + 1 / (s - 1) := by
  obtain ⟨C, hC, hbound⟩ := zeta_logDerivative_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro s hs hs2
  have h := (Complex.re_le_norm
    (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1))).trans
    (hbound s hs hs2)
  have hid : (1 / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
    norm_cast
  rw [Complex.sub_re, hid] at h
  linarith

end Awei.W53

end

end

end SiegelZeros

end OAI
