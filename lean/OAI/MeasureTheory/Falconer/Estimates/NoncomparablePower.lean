import OAI.MeasureTheory.Falconer.Angular.StationaryPowerRate

namespace OAI

namespace PlanarFalconer

theorem noncomparable_power_absorption {c : ℝ} (hc : 0 < c) (T : ℝ) :
    ∃ q : ℕ, ∀ H : ℝ, 0 ≤ H → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ A : ℝ, ((2:ℝ)^N)^c ≤ A →
      H*A^(-1/2:ℝ)/(A/2)^q ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨q,hq⟩ := exists_nat_gt ((T+1)/c)
  have hq' : T+1 < (q:ℝ)*c := (div_lt_iff₀ hc).mp hq
  refine ⟨q,?_⟩
  intro H hH
  obtain ⟨N₀,h₀⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (H*2^q)
  refine ⟨N₀,?_⟩
  intro N hN A hA
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : 0 < (2:ℝ)^N := by positivity
  have hA1 : 1 ≤ A := (Real.one_le_rpow hR hc.le).trans hA
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hconst : H*2^q ≤ (2:ℝ)^N := by simpa using h₀ N hN
  have hgain : A^(-1/2:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by norm_num)
  calc
    _ ≤ H/(A/2)^q := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa using mul_le_mul_of_nonneg_left hgain hH
    _ = (H*2^q)/A^q := by rw [div_pow,div_div_eq_mul_div]
    _ ≤ ((2:ℝ)^N)/(((2:ℝ)^N)^c)^q :=
      div_le_div₀ (by positivity) hconst (by positivity) (pow_le_pow_left₀ (by positivity) hA q)
    _ = ((2:ℝ)^N)^(1-c*(q:ℝ)) := by
      rw [← Real.rpow_mul_natCast hRp.le]
      nth_rw 1 [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_sub hRp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by nlinarith)

end PlanarFalconer

end OAI
