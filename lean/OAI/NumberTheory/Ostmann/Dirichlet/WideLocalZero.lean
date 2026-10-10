import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import StrongPNT.Erdos970.PNT2_LogDerivative

namespace OAI

open Erdos970

namespace Ostmann.Dirichlet
open Filter
open scoped Topology BigOperators

theorem exists_wide_local_zero_log_derivative_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 < B → ∀ f : ℂ → ℂ,
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z) →
      f 0 = 1 → (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖f z‖ ≤ B) →
      ∃ S : Finset ℂ, (∀ z, z ∈ S ↔ ‖z‖ ≤ 49/50 ∧ f z = 0) ∧
        ∀ z : ℂ, ‖z‖ ≤ 19/20 → f z ≠ 0 →
          ‖deriv f z / f z - ∑ rho ∈ S, (analyticOrderAt f rho).toNat / (z-rho)‖ ≤
            C * Real.log B := by
  classical
  let K : ℝ := 16 * (97/100)^2 / (((97/100)-(19/20))^3) +
    1 / (((99/100)^2/(49/50)-(49/50)) * Real.log ((99/100)/(49/50)))
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro B hB f hf hf0 hfB
  have hfne : f 0 ≠ 0 := by rw [hf0]; norm_num
  have hfinite : (zerosetKfR (49/50) (by norm_num) f).Finite :=
    lem_Contra_finiteKR (49/50) (by norm_num) (by norm_num) f hf ⟨0, by simp, hfne⟩
  have hex (rho : ℂ) : ∃ g : ℂ → ℂ,
      rho ∈ zerosetKfR (49/50) (by norm_num) f →
      AnalyticAt ℂ g rho ∧ g rho ≠ 0 ∧
      ∀ᶠ z in 𝓝 rho, f z = (z-rho)^(analyticOrderAt f rho).toNat * g z := by
    by_cases hr : rho ∈ zerosetKfR (49/50) (by norm_num) f
    · obtain ⟨g, hg⟩ := lem_analytic_zero_factor (99/100) (49/50)
        (by norm_num) (by norm_num) (by norm_num) f hf hfne rho hr
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ => 1, fun h => (hr h).elim⟩
  choose g hg using hex
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro z
    simp only [Set.Finite.mem_toFinset, zerosetKfR, Set.mem_ofPred_eq,
      Metric.mem_closedBall, dist_zero_right]
  · intro z hz hzne
    have hz' : z ∈ Metric.closedBall (0 : ℂ) (19/20) \
        zerosetKfR (49/50) (by norm_num) f := by
      refine ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, ?_⟩
      intro h
      exact hzne h.2
    have h := final_ineq1 B hB (19/20) (97/100) (99/100) (49/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      f hf hf0 hfinite hg
      (fun w hw => hfB w ((Metric.closedBall_subset_closedBall (by norm_num : (99/100:ℝ) ≤ 1)) hw)) z hz'
    apply h.trans
    exact mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) K) (Real.log_pos hB).le

end Ostmann.Dirichlet

end OAI
