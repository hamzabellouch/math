import OAI.MeasureTheory.Falconer.Angular.LocalizedStationaryExpansion

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem stationary_remainder_factor (n : ℕ) (Λ A C D : ℝ) :
    ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))*(A*C*D^(2*(n+1)+2)) =
      (((2*Real.pi^2)^(n+1)/(n.factorial:ℝ))*A)*C*D^2*(D^2/Λ)^(n+1) := by
  have he : Real.pi^2/(Λ/2) = (2*Real.pi^2)/Λ := by ring
  rw [he,div_pow,div_pow,pow_add D (2*(n+1)) 2,pow_mul D 2 (n+1)]
  ring

 theorem localized_stationary_ratio_remainder (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {Λ C D : ℝ}, 0 < Λ → 0 ≤ C → 1 ≤ D →
    (∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖localizedCircleIntegral Λ f - Complex.exp (Complex.I*(Λ:ℂ)) *
      (fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ)‖ ≤
    (Real.pi/(Λ/2))^(1/2:ℝ) * (A*C*D^2*(D^2/Λ)^(n+1)) := by
  obtain ⟨A,hA,hh⟩ := localized_stationary_uniform_remainder n
  refine ⟨((2*Real.pi^2)^(n+1)/(n.factorial:ℝ))*A,by positivity,?_⟩
  intro f hf Λ C D hΛ hC hD hb
  have h := hh hf hΛ hC hD hb
  rw [mul_assoc,stationary_remainder_factor] at h
  exact h

 theorem stationary_slack_power {R D Λ c sig : ℝ} (hR : 1 ≤ R) (hD : 0 ≤ D)
    (hΛ : 0 < Λ) (hupper : D ≤ R^(1+sig))
    (hratio : D^2/Λ ≤ R^(-c*sig)) (J : ℕ) :
    D^2*(D^2/Λ)^J ≤ R^(2+2*sig-c*sig*(J:ℝ)) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  calc
    _ ≤ (R^(1+sig))^2*(R^(-c*sig))^J :=
      mul_le_mul (pow_le_pow_left₀ hD hupper 2)
        (pow_le_pow_left₀ (by positivity) hratio J) (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hRp.le,← Real.rpow_mul_natCast hRp.le,← Real.rpow_add hRp]
      congr 1
      push_cast
      ring

end PlanarFalconer

end OAI
