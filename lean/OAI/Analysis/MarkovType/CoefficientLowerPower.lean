import OAI.Analysis.MarkovType.CoefficientThresholdCount
import OAI.Analysis.MarkovType.CoefficientQuotientGain
import OAI.Analysis.MarkovType.GeometricThresholdPowerSum

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coefficientBasic_lower_power_of_half_gain {M q : ℕ} {K : ℝ}
    (hM : 0 < M) (hK : 0 ≤ K) (hq : 1 ≤ q)
    (hratio : (M : ℝ) * (1 / 2 : ℝ) ^ q < 1)
    (hgain : ∀ y : Fin M → E, CoefficientBasic K y →
      ∃ i, ‖y i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, y j‖)
    {n : ℕ} (x : Fin n → E) (hx : CoefficientBasic K x) :
    (∑ i, ‖x i‖ ^ q) ≤
      ((2 * K) ^ q * (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ q))) *
        ‖∑ i, x i‖ ^ q := by
  classical
  let A : ℝ := (2 * K) * ‖∑ i, x i‖
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num) hK) (norm_nonneg _)
  have hcount (k : ℕ) :
      (Finset.univ.filter (fun i => A * (1 / 2 : ℝ) ^ k < ‖x i‖)).card ≤ M ^ k := by
    have heq : A * (1 / 2 : ℝ) ^ k =
        (2 * K) * (1 / 2 : ℝ) ^ k * ‖∑ i, x i‖ := by dsimp [A]; ring
    rw [heq]
    exact (coefficientBasic_card_large_lt_pow hM hK hgain x hx k).le
  have hsum := sum_pow_le_of_geometric_threshold_count hq hA hratio
    (fun i => ‖x i‖) (fun i => norm_nonneg _) (fun i => hx.norm_entry_le i) hcount
  calc
    (∑ i, ‖x i‖ ^ q) ≤
        A ^ q * (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ q)) := hsum
    _ = _ := by dsimp [A]; rw [mul_pow]; ring

theorem half_gain_power_ratio_lt_one (M : ℕ) :
    (M : ℝ) * (1 / 2 : ℝ) ^ M < 1 := by
  have hp : (M : ℝ) < (2 : ℝ) ^ M := by
    exact_mod_cast M.lt_pow_self (by decide : 1 < 2)
  have hden : (0 : ℝ) < 2 ^ M := pow_pos (by norm_num) M
  have h := (div_lt_one hden).mpr hp
  simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using h

theorem FiniteTriangularObstruction.coefficient_lower_power
    (hE : FiniteTriangularObstruction E) {K : ℝ} (hK : 1 < K) :
    ∃ q : ℕ, 2 ≤ q ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ) (x : Fin n → E), CoefficientBasic K x →
        (∑ i, ‖x i‖ ^ q) ≤ D * ‖∑ i, x i‖ ^ q := by
  obtain ⟨M, hM, hgain⟩ := hE.coefficient_half_gain hK
  have hMpos : 0 < M := lt_of_lt_of_le (by decide : 0 < 2) hM
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  have hr := half_gain_power_ratio_lt_one M
  let D : ℝ := (2 * K) ^ M *
    (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ M))
  have hD : 0 < D := by
    have hden : 0 < 1 - (M : ℝ) * (1 / 2 : ℝ) ^ M := sub_pos.mpr hr
    have hfrac : 0 ≤ (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ M) :=
      div_nonneg (Nat.cast_nonneg M) hden.le
    exact mul_pos (pow_pos (mul_pos (by norm_num) hKpos) M) (by linarith)
  refine ⟨M, hM, D, hD, ?_⟩
  intro n x hx
  exact coefficientBasic_lower_power_of_half_gain hMpos hKpos.le
    (le_trans (by decide : 1 ≤ 2) hM) hr hgain x hx

theorem FiniteTriangularObstruction.coefficient_lower_power_quotients
    (hE : FiniteTriangularObstruction E) {K : ℝ} (hK : 1 < K) :
    ∃ q : ℕ, 2 ≤ q ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (F : Submodule ℝ E) [IsClosed (F : Set E)] (n : ℕ) (x : Fin n → E ⧸ F),
        CoefficientBasic K x → (∑ i, ‖x i‖ ^ q) ≤ D * ‖∑ i, x i‖ ^ q := by
  obtain ⟨M, hM, hgain⟩ := hE.coefficient_half_gain_quotients hK
  have hMpos : 0 < M := lt_of_lt_of_le (by decide : 0 < 2) hM
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  have hr := half_gain_power_ratio_lt_one M
  let D : ℝ := (2 * K) ^ M *
    (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ M))
  have hD : 0 < D := by
    have hden : 0 < 1 - (M : ℝ) * (1 / 2 : ℝ) ^ M := sub_pos.mpr hr
    have hfrac : 0 ≤ (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ M) :=
      div_nonneg (Nat.cast_nonneg M) hden.le
    exact mul_pos (pow_pos (mul_pos (by norm_num) hKpos) M) (by linarith)
  refine ⟨M, hM, D, hD, ?_⟩
  intro F _ n x hx
  exact coefficientBasic_lower_power_of_half_gain hMpos hKpos.le
    (le_trans (by decide : 1 ≤ 2) hM) hr (hgain F) x hx

end MarkovSuperreflexivity

end OAI
