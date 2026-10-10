import OAI.MeasureTheory.Falconer.Angular.AngularFarStationaryScale

namespace OAI

namespace PlanarFalconer

theorem root_symbol_scale_square {sig : ℝ} (hsig : 0 ≤ sig) (hsmall : sig ≤ 1/4)
    (N L : ℕ) (hL : 2*L ≤ N) :
    sourceSymbolScale N sig L^2 ≤ ((2:ℝ)^N)^(1-2*sig) := by
  have hL' : 2*(L:ℝ) ≤ (N:ℝ) := by exact_mod_cast hL
  have hn := Nat.cast_nonneg (α := ℝ) N
  have hns := mul_nonneg hn hsig
  have hbase : sourceSymbolScale N sig L ≤ (2:ℝ)^((N:ℝ)*(1/2-sig)) := by
    rw [sourceSymbolScale_dyadic]
    apply max_le <;> apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    · nlinarith [mul_nonneg hn (sub_nonneg.mpr hsmall)]
    · nlinarith
  apply (pow_le_pow_left₀ (sourceSymbolScale_pos N sig L).le hbase 2).trans_eq
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem root_frequency_lower {sig δ : ℝ} (hsig : 0 < sig) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ r d : ℝ,
    (2:ℝ)^((N:ℝ)-1) ≤ r → δ ≤ d →
    ((2:ℝ)^N)^(1-sig) ≤ r*d := by
  obtain ⟨N₀,h₀⟩ := fixed_constant_absorbed hsig (2/δ)
  refine ⟨N₀,?_⟩
  intro N hN r d hr hd
  have hconst := (div_le_iff₀ hδ).mp (h₀ N hN)
  have hprod : (2:ℝ)^N/2*δ ≤ r*d := by
    have hr' : (2:ℝ)^N/2 ≤ r := by
      simpa [Real.rpow_sub (by norm_num : (0:ℝ) < 2)] using hr
    exact mul_le_mul hr' hd hδ.le ((by positivity : 0 < (2:ℝ)^N/2).trans_le hr').le
  apply le_trans _ hprod
  have hp : 0 < ((2:ℝ)^N)^sig := by positivity
  rw [Real.rpow_sub (by positivity : (0:ℝ) < (2:ℝ)^N),Real.rpow_one]
  apply (div_le_iff₀ hp).mpr
  have hh := mul_le_mul_of_nonneg_left hconst (by positivity : 0 ≤ (2:ℝ)^N/2)
  nlinarith

theorem root_stationary_slack {sig δ : ℝ} (hsig : 0 < sig) (hsmall : sig ≤ 1/4)
    (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 2*L ≤ N → ∀ r d : ℝ,
    (2:ℝ)^((N:ℝ)-1) ≤ r → δ ≤ d →
    ((2:ℝ)^N)^sig ≤ r*d ∧
    sourceSymbolScale N sig L^2/(r*d) ≤ ((2:ℝ)^N)^(-sig) := by
  obtain ⟨N₀,h₀⟩ := root_frequency_lower hsig hδ
  refine ⟨N₀,?_⟩
  intro N hN L hL r d hr hd
  have hΛ := h₀ N hN r d hr hd
  have hΛpos : 0 < r*d := (by positivity : 0 < ((2:ℝ)^N)^(1-sig)).trans_le hΛ
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  refine ⟨(Real.rpow_le_rpow_of_exponent_le hR (by linarith : sig ≤ 1-sig)).trans hΛ,?_⟩
  apply (div_le_iff₀ hΛpos).mpr
  calc
    _ ≤ ((2:ℝ)^N)^(1-2*sig) := root_symbol_scale_square hsig.le hsmall N L hL
    _ = ((2:ℝ)^N)^(-sig)*((2:ℝ)^N)^(1-sig) := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hΛ (by positivity)

end PlanarFalconer

end OAI
