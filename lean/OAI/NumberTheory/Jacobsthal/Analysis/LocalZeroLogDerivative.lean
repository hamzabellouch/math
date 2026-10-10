import OAI.NumberTheory.Jacobsthal.Primes.UniformDirichletBasepoint

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

theorem exists_local_zero_log_derivative_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 < B → ∀ f : ℂ → ℂ,
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z) →
      f 0 = 1 → (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖f z‖ ≤ B) →
      ∃ S : Finset ℂ, (∀ z, z ∈ S ↔ ‖z‖ ≤ 19/20 ∧ f z = 0) ∧
        ∀ z : ℂ, ‖z‖ ≤ 17/20 → f z ≠ 0 →
          ‖deriv f z / f z - ∑ rho ∈ S, (analyticOrderAt f rho).toNat / (z-rho)‖ ≤
            C * Real.log B := by
  classical
  let K : ℝ := 16 * (9/10)^2 / (((9/10)-(17/20))^3) +
    1 / (((39/40)^2/(19/20)-(19/20)) * Real.log ((39/40)/(19/20)))
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro B hB f hf hf0 hfB
  have hfne : f 0 ≠ 0 := by rw [hf0]; norm_num
  have hfinite : (_root_.Erdos970.zerosetKfR (19/20) (by norm_num) f).Finite :=
    _root_.Erdos970.lem_Contra_finiteKR (19/20) (by norm_num) (by norm_num) f hf ⟨0, by simp, hfne⟩
  have hex (rho : ℂ) : ∃ g : ℂ → ℂ,
      rho ∈ _root_.Erdos970.zerosetKfR (19/20) (by norm_num) f →
      AnalyticAt ℂ g rho ∧ g rho ≠ 0 ∧
      ∀ᶠ z in 𝓝 rho, f z = (z-rho)^(analyticOrderAt f rho).toNat * g z := by
    by_cases hr : rho ∈ _root_.Erdos970.zerosetKfR (19/20) (by norm_num) f
    · obtain ⟨g, hg⟩ := _root_.Erdos970.lem_analytic_zero_factor (39/40) (19/20)
        (by norm_num) (by norm_num) (by norm_num) f hf hfne rho hr
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ => 1, fun h => (hr h).elim⟩
  choose g hg using hex
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro z
    simp only [Set.Finite.mem_toFinset, _root_.Erdos970.zerosetKfR, Set.mem_ofPred_eq,
      Metric.mem_closedBall, dist_zero_right]
  · intro z hz hzne
    have hz' : z ∈ Metric.closedBall (0 : ℂ) (17/20) \
        _root_.Erdos970.zerosetKfR (19/20) (by norm_num) f := by
      refine ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, ?_⟩
      intro h
      exact hzne h.2
    have h := _root_.Erdos970.final_ineq1 B hB (17/20) (9/10) (39/40) (19/20)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      f hf hf0 hfinite hg
      (fun w hw => hfB w ((Metric.closedBall_subset_closedBall (by norm_num : (39/40:ℝ) ≤ 1)) hw)) z hz'
    apply h.trans
    exact mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) K) (Real.log_pos hB).le

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
