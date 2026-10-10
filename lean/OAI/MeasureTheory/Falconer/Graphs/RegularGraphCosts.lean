import OAI.MeasureTheory.Falconer.Graphs.RegularGraphObstruction

namespace OAI

/-! Polynomial losses in the refined graph obstruction, specialized to a
single weak scale parameter. -/
namespace Falconer

noncomputable def regularGraphCost (M : ℕ) : ℝ :=
  1+1024*(2*(M:ℝ)+3)^2+4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2+
    2*(1+4*(M:ℝ))^2+2*(M:ℝ)^2

 theorem regularGraphCost_one_le (M : ℕ) : 1 ≤ regularGraphCost M := by
  have hh : 0 ≤ 1024*(2*(M:ℝ)+3)^2+4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2+
      2*(1+4*(M:ℝ))^2+2*(M:ℝ)^2 := by positivity
  unfold regularGraphCost
  linarith

 theorem regular_graph_weak_costs {κ t R : ℝ} (hκ : κ ≤ 1) (ht : t ≤ 2)
    (M : ℕ) (hM : 1 ≤ M) (hR : 1 ≤ R) :
    1024*(2*(M:ℝ)+3)^2*R^4/(R⁻¹)^6 ≤ regularGraphCost M*R^20 ∧
    4096*(2*((M*M:ℕ):ℝ)+3)*(2*(M:ℝ)+3)^2*R^4/(R⁻¹)^13 ≤ regularGraphCost M*R^20 ∧
    Real.sqrt ((2*(R/R⁻¹)*R*(R/(R⁻¹)^2)/R⁻¹)*(1+4*(M:ℝ))^t) ≤ regularGraphCost M*R^20 ∧
    (2/(R⁻¹)^4)*R*(M:ℝ)^(2*κ) ≤ regularGraphCost M*R^20 := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : 0 ≤ (M:ℝ) := Nat.cast_nonneg _
  have hC := regularGraphCost_one_le M
  have hD : 1024*(2*(M:ℝ)+3)^2 ≤ regularGraphCost M := by
    unfold regularGraphCost
    nlinarith [sq_nonneg (M:ℝ),sq_nonneg (1+4*(M:ℝ))]
  have hQ : 4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2 ≤ regularGraphCost M := by
    unfold regularGraphCost
    nlinarith [sq_nonneg (M:ℝ),sq_nonneg (1+4*(M:ℝ)),sq_nonneg (2*(M:ℝ)+3)]
  have hP : 2*(1+4*(M:ℝ))^2 ≤ regularGraphCost M := by
    have hh : 0 ≤ 1+1024*(2*(M:ℝ)+3)^2+
        4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2+2*(M:ℝ)^2 := by positivity
    unfold regularGraphCost
    linarith
  have hI : 2*(M:ℝ)^2 ≤ regularGraphCost M := by
    have hh : 0 ≤ 1+1024*(2*(M:ℝ)+3)^2+
        4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2+2*(1+4*(M:ℝ))^2 := by positivity
    unfold regularGraphCost
    linarith
  have hpow (n : ℕ) (hn : n ≤ 20) : R^n ≤ R^20 := pow_le_pow_right₀ hR hn
  have hCR : 1 ≤ regularGraphCost M*R^20 := by
    have hh := one_le_pow₀ hR (n := 20)
    nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · calc
      _ = (1024*(2*(M:ℝ)+3)^2)*R^10 := by rw [inv_pow,div_inv_eq_mul]; ring
      _ ≤ regularGraphCost M*R^20 := mul_le_mul hD (hpow 10 (by omega)) (by positivity) (by linarith)
  · calc
      _ = (4096*(2*(M:ℝ)^2+3)*(2*(M:ℝ)+3)^2)*R^17 := by
        rw [inv_pow,div_inv_eq_mul,Nat.cast_mul]; ring
      _ ≤ regularGraphCost M*R^20 := mul_le_mul hQ (hpow 17 (by omega)) (by positivity) (by linarith)
  · have he : 2*(R/R⁻¹)*R*(R/(R⁻¹)^2)/R⁻¹ = 2*R^7 := by
      field_simp
    have hp : (1+4*(M:ℝ))^t ≤ (1+4*(M:ℝ))^2 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ 1+4*(M:ℝ)) ht
      simpa only [Real.rpow_two] using hh
    have hb : (2*R^7)*(1+4*(M:ℝ))^t ≤ regularGraphCost M*R^20 := by
      calc
        _ ≤ (2*R^7)*(1+4*(M:ℝ))^2 := mul_le_mul_of_nonneg_left hp (by positivity)
        _ = (2*(1+4*(M:ℝ))^2)*R^7 := by ring
        _ ≤ _ := mul_le_mul hP (hpow 7 (by omega)) (by positivity) (by linarith)
    rw [he]
    exact (Real.sqrt_le_sqrt hb).trans (Real.sqrt_le_self_iff.mpr (Or.inr hCR))
  · have hp : (M:ℝ)^(2*κ) ≤ (M:ℝ)^2 := by
      have hh := Real.rpow_le_rpow_of_exponent_le hM1 (by linarith : 2*κ ≤ 2)
      simpa only [Real.rpow_two] using hh
    calc
      _ = (2*R^5)*(M:ℝ)^(2*κ) := by rw [inv_pow,div_inv_eq_mul]; ring
      _ ≤ (2*R^5)*(M:ℝ)^2 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (2*(M:ℝ)^2)*R^5 := by ring
      _ ≤ _ := mul_le_mul hI (hpow 5 (by omega)) (by positivity) (by linarith)

end Falconer

end OAI
