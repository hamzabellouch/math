import OAI.MeasureTheory.Falconer.Angular.InverseCircleAssembly

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

theorem inverse_circle_stationary_power {c sig T : ℝ} (hc : 0 < c) (hsig : 0 < sig) :
    ∃ n : ℕ, ∀ P C : ℝ, 0 ≤ P → 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ψ =ᶠ[𝓝 0] (fun _ => 1) → ψ =ᶠ[𝓝 Real.pi] (fun _ => 0) →
    ∀ {D Λ : ℝ}, 1 ≤ D → ((2:ℝ)^N)^(c*sig) ≤ Λ →
    D ≤ ((2:ℝ)^N)^(1+sig) → D^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖Complex.exp (Complex.I*(Λ:ℂ))*f 0 - inverseCircleIntegral n Λ ψ f‖ ≤
      ((2:ℝ)^N)^(-T) := by
  have hcs : 0 < c*sig := mul_pos hc hsig
  obtain ⟨n, hn⟩ := exists_nat_gt ((T+3+2*sig)/(c*sig))
  have hn' : T+3+2*sig < (n:ℝ)*(c*sig) := (div_lt_iff₀ hcs).mp hn
  have hexp : 2+2*sig-c*sig*((n+1:ℕ):ℝ) ≤ -T-1 := by push_cast; nlinarith
  obtain ⟨A,hA,hbound⟩ := inverse_circle_ratio_remainder n
  refine ⟨n, ?_⟩
  intro P C hP hC
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ)<1) (A*P*C)
  refine ⟨N₀, ?_⟩
  intro N hN ψ f hψ hf hpψ hpf hψ₀ hψπ D Λ hD hlower hupper hratio hbψ hbf
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : 0 < (2:ℝ)^N := by positivity
  have hΛ : 1 ≤ Λ := (Real.one_le_rpow hR hcs.le).trans hlower
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hr : D^2/Λ ≤ 1 := hratio.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hR (by nlinarith))
  have hpow : D^2*(D^2/Λ)^(n+1) ≤ ((2:ℝ)^N)^(-T-1) :=
    (stationary_slack_power hR (zero_le_one.trans hD) hΛp hupper hratio (n+1)).trans
      (Real.rpow_le_rpow_of_exponent_le hR hexp)
  have hconst : A*P*C ≤ (2:ℝ)^N := by simpa using hN₀ N hN
  rw [norm_sub_rev]
  apply (hbound hψ hf hpψ hpf hψ₀ hψπ hP hC hD hΛ hr hbψ hbf).trans
  calc
    _ = (A*P*C)*(D^2*(D^2/Λ)^(n+1)) := by ring
    _ ≤ (2:ℝ)^N*((2:ℝ)^N)^(-T-1) :=
      mul_le_mul hconst hpow (by positivity) hRp.le
    _ = _ := by
      conv_lhs => arg 1; rw [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add hRp]
      congr 1
      ring

end PlanarFalconer

end OAI
