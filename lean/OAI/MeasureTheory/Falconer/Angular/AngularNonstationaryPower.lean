import OAI.MeasureTheory.Falconer.Angular.AngularNonstationary
import OAI.MeasureTheory.Falconer.Angular.StationaryPowerRate

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem angular_even_decay_factor (D Λ : ℝ) (J : ℕ) :
    D^(2*J)/Λ^(2*J) = (D^2/Λ)^J * (Λ^J)⁻¹ := by
  have hΛ : Λ^(2*J) = (Λ^J)^2 := by rw [← pow_mul]; congr 1; omega
  rw [pow_mul D 2 J,hΛ,div_pow]
  ring

 theorem angular_even_decay_half {Λ : ℝ} (hΛ : 1 ≤ Λ) {J : ℕ} (hJ : 1 ≤ J) :
    (Λ^J)⁻¹ ≤ Λ^(-1/2:ℝ) := by
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  rw [← Real.rpow_natCast,← Real.rpow_neg hΛp.le]
  apply Real.rpow_le_rpow_of_exponent_le hΛ
  have hJ' : (1:ℝ) ≤ J := by exact_mod_cast hJ
  linarith

 theorem angular_nonstationary_power_rate {η a b c sig T : ℝ}
    (hη : 0 < η) (hab : a ≤ b) (hc : 0 < c) (hsig : 0 < sig) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ C : ℝ, 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → tsupport f ⊆ Icc a b →
    (∀ x ∈ tsupport f, η ≤ |Real.sin x|) → ∀ {D Λ : ℝ}, 1 ≤ D →
    ((2:ℝ)^N)^(c*sig) ≤ Λ → D^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
    (∀ k ≤ 2*J, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ x * f x‖ ≤ Λ^(-1/2:ℝ) * ((2:ℝ)^N)^(-T) := by
  have hcs : 0 < c*sig := mul_pos hc hsig
  obtain ⟨j,hj⟩ := exists_nat_gt ((T+1)/(c*sig))
  have hj' : T+1 < (j:ℝ)*(c*sig) := (div_lt_iff₀ hcs).mp hj
  have hexp : -c*sig*((j+1:ℕ):ℝ) ≤ -T-1 := by push_cast; nlinarith
  obtain ⟨A,hA,hbound⟩ := angular_nonstationary_uniform hη hab (2*(j+1))
  refine ⟨j+1,by omega,?_⟩
  intro C hC
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ)<1) (A*C)
  refine ⟨N₀,?_⟩
  intro N hN f hf hs haway D Λ hD hlower hratio hb
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : 0 < (2:ℝ)^N := by positivity
  have hΛ : 1 ≤ Λ := (Real.one_le_rpow hR hcs.le).trans hlower
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hpow : (D^2/Λ)^(j+1) ≤ ((2:ℝ)^N)^(-T-1) := by
    calc
      _ ≤ (((2:ℝ)^N)^(-c*sig))^(j+1) := pow_le_pow_left₀ (by positivity) hratio _
      _ = ((2:ℝ)^N)^(-c*sig*((j+1:ℕ):ℝ)) := (Real.rpow_mul_natCast hRp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR hexp
  have hAC : A*C ≤ (2:ℝ)^N := by simpa using hN₀ N hN
  apply (hbound hf hs haway hC hD hΛp hb).trans
  calc
    _ = (A*C)*((D^2/Λ)^(j+1)*(Λ^(j+1))⁻¹) := by
      rw [← angular_even_decay_factor]
      ring
    _ ≤ (2:ℝ)^N * (((2:ℝ)^N)^(-T-1)*Λ^(-1/2:ℝ)) := by
      apply mul_le_mul hAC
        (mul_le_mul hpow (angular_even_decay_half hΛ (by omega)) (by positivity) (by positivity))
        (by positivity) hRp.le
    _ = _ := by
      rw [← mul_assoc]
      conv_lhs => arg 1; arg 1; rw [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add hRp]
      have he : (1:ℝ)+(-T-1) = -T := by ring
      rw [he,mul_comm]

end PlanarFalconer

end OAI
