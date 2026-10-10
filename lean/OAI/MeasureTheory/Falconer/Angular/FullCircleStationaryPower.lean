import OAI.MeasureTheory.Falconer.Angular.FullCircleStationaryExpansion
import OAI.MeasureTheory.Falconer.Angular.AngularNonstationaryPower

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff

 theorem quadratic_scale_half {Λ : ℝ} (hΛ : 0 < Λ) :
    (Real.pi/(Λ/2))^(1/2:ℝ) = Λ^(-1/2:ℝ)*Real.sqrt (2*Real.pi) := by
  have he : Real.pi/(Λ/2) = (2*Real.pi)/Λ := by ring
  rw [he,Real.div_rpow (by positivity) hΛ.le,Real.sqrt_eq_rpow]
  rw [show (-1/2:ℝ) = -(1/2:ℝ) by ring,Real.rpow_neg hΛ.le]
  ring

 theorem full_circle_stationary_power {c sig T : ℝ} (hc : 0 < c) (hsig : 0 < sig) :
    ∃ n : ℕ, ∀ C : ℝ, 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → Function.Periodic f (2*Real.pi) →
    ∀ {D Λ : ℝ}, 1 ≤ D → ((2:ℝ)^N)^(c*sig) ≤ Λ →
    D ≤ ((2:ℝ)^N)^(1+sig) → D^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
    (∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖(∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ*f θ) - fullCircleStationaryExpansion Λ f n‖ ≤
      Λ^(-1/2:ℝ)*((2:ℝ)^N)^(-T) := by
  have hcs : 0 < c*sig := mul_pos hc hsig
  obtain ⟨n,hn⟩ := exists_nat_gt ((T+3+2*sig)/(c*sig))
  have hn' : T+3+2*sig < (n:ℝ)*(c*sig) := (div_lt_iff₀ hcs).mp hn
  have hexp : 2+2*sig-c*sig*((n+1:ℕ):ℝ) ≤ -T-1 := by push_cast; nlinarith
  have hexp' : -c*sig*((n+1:ℕ):ℝ) ≤ -T-1 := by push_cast; nlinarith
  obtain ⟨A,B,hA,hB,hbound⟩ := full_circle_stationary_expansion n (2*(n+1))
  refine ⟨n,?_⟩
  intro C hC
  let K : ℝ := Real.sqrt (2*Real.pi)*(((2*Real.pi^2)^(n+1)/(n.factorial:ℝ))*A)*C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ)<1) (K+B*C)
  refine ⟨N₀,?_⟩
  intro N hN f hf hp D Λ hD hlower hupper hratio hb
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : 0 < (2:ℝ)^N := by positivity
  have hΛ : 1 ≤ Λ := (Real.one_le_rpow hR hcs.le).trans hlower
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hp₀ : D^2*(D^2/Λ)^(n+1) ≤ ((2:ℝ)^N)^(-T-1) :=
    (stationary_slack_power hR (zero_le_one.trans hD) hΛp hupper hratio (n+1)).trans
      (Real.rpow_le_rpow_of_exponent_le hR hexp)
  have hp₁ : (D^2/Λ)^(n+1) ≤ ((2:ℝ)^N)^(-T-1) := by
    calc
      _ ≤ (((2:ℝ)^N)^(-c*sig))^(n+1) := pow_le_pow_left₀ (by positivity) hratio _
      _ = ((2:ℝ)^N)^(-c*sig*((n+1:ℕ):ℝ)) := (Real.rpow_mul_natCast hRp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR hexp'
  have hconst : K+B*C ≤ (2:ℝ)^N := by simpa using hN₀ N hN
  have hh := hbound hf hp hΛp hC hD (by simpa [max_eq_left (by omega : 2*(n+1) ≤ 2*(n+1)+2)] using hb)
  apply hh.trans
  have hstat : ((Real.pi/(Λ/2))^(1/2:ℝ)*((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ)))*
      (A*C*D^(2*(n+1)+2)) ≤ Λ^(-1/2:ℝ)*K*((2:ℝ)^N)^(-T-1) := by
    rw [mul_assoc,stationary_remainder_factor,quadratic_scale_half hΛp]
    calc
      _ = (Λ^(-1/2:ℝ)*K)*(D^2*(D^2/Λ)^(n+1)) := by dsimp [K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₀ (by positivity)
  have hnon : B*C*D^(2*(n+1))/Λ^(2*(n+1)) ≤
      Λ^(-1/2:ℝ)*(B*C)*((2:ℝ)^N)^(-T-1) := by
    calc
      _ = (B*C)*((D^2/Λ)^(n+1)*(Λ^(n+1))⁻¹) := by rw [← angular_even_decay_factor]; ring
      _ ≤ (B*C)*(((2:ℝ)^N)^(-T-1)*Λ^(-1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hp₁ (angular_even_decay_half hΛ (by omega)) (by positivity) (by positivity))
          (mul_nonneg hB hC)
      _ = _ := by ring
  calc
    _ ≤ Λ^(-1/2:ℝ)*K*((2:ℝ)^N)^(-T-1) + Λ^(-1/2:ℝ)*(B*C)*((2:ℝ)^N)^(-T-1) :=
      add_le_add hstat hnon
    _ = Λ^(-1/2:ℝ)*((K+B*C)*((2:ℝ)^N)^(-T-1)) := by ring
    _ ≤ Λ^(-1/2:ℝ)*((2:ℝ)^N*((2:ℝ)^N)^(-T-1)) := by gcongr
    _ = _ := by
      congr 1
      conv_lhs => arg 1; rw [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add hRp]
      congr 1
      ring

end PlanarFalconer

end OAI
