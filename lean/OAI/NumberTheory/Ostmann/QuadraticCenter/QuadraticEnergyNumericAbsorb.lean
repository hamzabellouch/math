import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterSelection
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyComplete

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology
open Filter

theorem eventually_linear_cost_le_exp_K (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ K : ℝ, T^((3 : ℝ)/4) ≤ K →
      C*T ≤ Real.exp (ε*K) := by
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3/4)).bound (half_pos hε)
  have hc := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/4)).eventually_ge_atTop
    (2*Real.log C/ε)
  filter_upwards [hl, hc, eventually_ge_atTop (1 : ℝ)] with T hl hc hT
  intro K hK
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hpow : 0 ≤ T^((3 : ℝ)/4) := Real.rpow_nonneg hT0.le _
  have hl' : Real.log T ≤ ε/2*T^((3 : ℝ)/4) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hpow] using hl
  have hc' : Real.log C ≤ ε/2*T^((3 : ℝ)/4) := by
    have hh := (div_le_iff₀ hε).mp hc
    nlinarith
  have he : Real.log C+Real.log T ≤ ε*K := by nlinarith
  simpa only [Real.exp_add, Real.exp_log hC, Real.exp_log hT0] using Real.exp_le_exp.mpr he

theorem quadratic_large_energy_numeric_absorb {N z : ℝ} (k : ℕ)
    (hN : 0 ≤ N) (hz : 2000 ≤ Real.sqrt z)
    (hcost : N*(quadraticCorrelationConstant+cutoffFourierBound^2) ≤ Real.exp ((k : ℝ)/500)) :
    N*Real.exp (2*(k : ℝ)/Real.sqrt z) *
      (Real.exp ((k : ℝ)/200) * (quadraticCorrelationConstant *
        Real.exp ((k : ℝ)*((1/16 : ℝ)^2+2*(1/16 : ℝ)/Real.sqrt z))) +
      cutoffFourierBound^2 * Real.exp (-10*(k : ℝ)) * (1+(1/16 : ℝ))^(2*k)) ≤
      Real.exp ((12/1000 : ℝ)*k) := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hz0 : 0 < Real.sqrt z := by linarith
  have hC := quadraticCorrelationConstant_pos.le
  have hden : (17/8 : ℝ)/Real.sqrt z ≤ 17/16000 := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 17/8)
      (by norm_num : (0 : ℝ) < 2000) hz
    norm_num at hh ⊢
    exact hh
  have hlow : 2*(k : ℝ)/Real.sqrt z + (k : ℝ)/200 +
      (k : ℝ)*((1/16 : ℝ)^2+2*(1/16 : ℝ)/Real.sqrt z) ≤ (k : ℝ)/100 := by
    have hh := mul_le_mul_of_nonneg_left hden hk
    ring_nf at hh ⊢
    nlinarith
  have hden2 : (2 : ℝ)/Real.sqrt z ≤ 1/1000 := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 2000) hz
    norm_num at hh ⊢
    exact hh
  have hhigh : 2*(k : ℝ)/Real.sqrt z - 10*(k : ℝ)+(k : ℝ)/8 ≤ (k : ℝ)/100 := by
    have hh := mul_le_mul_of_nonneg_left hden2 hk
    ring_nf at hh ⊢
    nlinarith
  have hpow : (1+(1/16 : ℝ))^(2*k) ≤ Real.exp ((k : ℝ)/8) := by
    calc
      _ ≤ (Real.exp (1/16 : ℝ))^(2*k) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1/16 : ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hlo : Real.exp (2*(k : ℝ)/Real.sqrt z) *
      (Real.exp ((k : ℝ)/200) * (quadraticCorrelationConstant *
        Real.exp ((k : ℝ)*((1/16 : ℝ)^2+2*(1/16 : ℝ)/Real.sqrt z)))) ≤
      quadraticCorrelationConstant*Real.exp ((k : ℝ)/100) := by
    calc
      _ = quadraticCorrelationConstant * Real.exp (2*(k : ℝ)/Real.sqrt z + (k : ℝ)/200 +
          (k : ℝ)*((1/16 : ℝ)^2+2*(1/16 : ℝ)/Real.sqrt z)) := by rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlow) hC
  have hhi : Real.exp (2*(k : ℝ)/Real.sqrt z) *
      (cutoffFourierBound^2*Real.exp (-10*(k : ℝ))*(1+(1/16 : ℝ))^(2*k)) ≤
      cutoffFourierBound^2*Real.exp ((k : ℝ)/100) := by
    calc
      _ ≤ Real.exp (2*(k : ℝ)/Real.sqrt z) *
          (cutoffFourierBound^2*Real.exp (-10*(k : ℝ))*Real.exp ((k : ℝ)/8)) := by gcongr
      _ = cutoffFourierBound^2*Real.exp (2*(k : ℝ)/Real.sqrt z-10*(k : ℝ)+(k : ℝ)/8) := by
        rw [Real.exp_add, Real.exp_sub, show (-10 : ℝ)*(k : ℝ) = -(10*(k : ℝ)) by ring, Real.exp_neg]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hhigh) (sq_nonneg _)
  calc
    _ = N*(Real.exp (2*(k : ℝ)/Real.sqrt z) *
        (Real.exp ((k : ℝ)/200) * (quadraticCorrelationConstant *
          Real.exp ((k : ℝ)*((1/16 : ℝ)^2+2*(1/16 : ℝ)/Real.sqrt z)))) +
        Real.exp (2*(k : ℝ)/Real.sqrt z) *
          (cutoffFourierBound^2*Real.exp (-10*(k : ℝ))*(1+(1/16 : ℝ))^(2*k))) := by ring
    _ ≤ N*(quadraticCorrelationConstant*Real.exp ((k : ℝ)/100)+
        cutoffFourierBound^2*Real.exp ((k : ℝ)/100)) := mul_le_mul_of_nonneg_left (add_le_add hlo hhi) hN
    _ = (N*(quadraticCorrelationConstant+cutoffFourierBound^2))*Real.exp ((k : ℝ)/100) := by ring
    _ ≤ Real.exp ((k : ℝ)/500)*Real.exp ((k : ℝ)/100) :=
      mul_le_mul_of_nonneg_right hcost (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann.QuadraticCenter

end

end OAI
