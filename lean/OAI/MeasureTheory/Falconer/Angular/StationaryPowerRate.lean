import OAI.MeasureTheory.Falconer.Angular.StationaryRemainderScale
import OAI.MeasureTheory.Falconer.Angular.ActualStationaryAmplitude

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem sourceSymbolScale_upper (N : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) {L : ℕ} (hL : L ≤ N) :
    sourceSymbolScale N sig L ≤ ((2:ℝ)^N)^(1+sig) := by
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRpos : 0 < (2:ℝ)^N := by positivity
  have hm : max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*sig)) ≤ (2:ℝ)^N := by
    apply max_le hR
    calc
      _ ≤ (2:ℝ)^N * 1 :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hL)
          (Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)) (by positivity) (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ ((2:ℝ)^N)^sig * (2:ℝ)^N := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by
      conv_lhs => arg 2; rw [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add hRpos]
      congr 1
      ring

 theorem localized_stationary_power_rate {c sig T : ℝ} (hc : 0 < c) (hsig : 0 < sig) :
    ∃ n : ℕ, ∀ C : ℝ, 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ {D Λ : ℝ}, 1 ≤ D → 0 < Λ →
    D ≤ ((2:ℝ)^N)^(1+sig) → D^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
    (∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖localizedCircleIntegral Λ f - Complex.exp (Complex.I*(Λ:ℂ)) *
      (fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ)‖ ≤
    (Real.pi/(Λ/2))^(1/2:ℝ) * ((2:ℝ)^N)^(-T) := by
  have hcs : 0 < c*sig := mul_pos hc hsig
  obtain ⟨n,hn⟩ := exists_nat_gt ((T+3+2*sig)/(c*sig))
  have hn' : T+3+2*sig < (n:ℝ)*(c*sig) := (div_lt_iff₀ hcs).mp hn
  have hexp : 2+2*sig-c*sig*((n+1:ℕ):ℝ) ≤ -T-1 := by
    push_cast
    nlinarith
  obtain ⟨A,hA,hbound⟩ := localized_stationary_ratio_remainder n
  refine ⟨n,?_⟩
  intro C hC
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (A*C)
  refine ⟨N₀,?_⟩
  intro N hN f hf D Λ hD hΛ hupper hratio hb
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : 0 < (2:ℝ)^N := by positivity
  have hs := stationary_slack_power hR (zero_le_one.trans hD) hΛ hupper hratio (n+1)
  have hpow : D^2*(D^2/Λ)^(n+1) ≤ ((2:ℝ)^N)^(-T-1) :=
    hs.trans (Real.rpow_le_rpow_of_exponent_le hR hexp)
  have hAC : A*C ≤ (2:ℝ)^N := by simpa using hN₀ N hN
  apply (hbound hf hΛ hC hD hb).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ = (A*C)*(D^2*(D^2/Λ)^(n+1)) := by ring
    _ ≤ (2:ℝ)^N * ((2:ℝ)^N)^(-T-1) :=
      mul_le_mul hAC hpow (by positivity) hRp.le
    _ = _ := by
      conv_lhs => arg 1; rw [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add hRp]
      congr 1
      ring

end PlanarFalconer

end OAI
