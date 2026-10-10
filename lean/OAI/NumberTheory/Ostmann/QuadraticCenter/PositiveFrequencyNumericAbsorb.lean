import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyMertens
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyNumericScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology
open Filter

theorem eventually_positive_array_euler_cost (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (u H : ℝ),
      0 ≤ u → u ≤ T^((1 : ℝ)/100000) → T/2 ≤ H →
      u*(3*Real.log T+C) ≤ H/10 := by
  filter_upwards [eventually_const_add_log_le_rpow C 3 (by norm_num : (0 : ℝ) < 1/2),
    eventually_mul_rpow_le_rpow 10 (a := 1/100000+1/2) (b := 1) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with T hlog hpow hT
  intro u H hu huup hH
  have hT0 : 0 < T := by linarith
  have hh : u*(3*Real.log T+C) ≤ T^((1 : ℝ)/100000)*(T^((1 : ℝ)/2)/2) := by
    calc
      _ ≤ u*(T^((1 : ℝ)/2)/2) := mul_le_mul_of_nonneg_left (by linarith [hlog]) hu
      _ ≤ _ := mul_le_mul_of_nonneg_right huup (by positivity)
  have hid : T^((1 : ℝ)/100000)*(T^((1 : ℝ)/2)/2) = T^((1 : ℝ)/100000+1/2)/2 := by
    rw [← mul_div_assoc, ← Real.rpow_add hT0]
  rw [hid] at hh
  rw [Real.rpow_one] at hpow
  linarith

theorem positive_array_envelope_sq_le_exp {L : ℕ} (hL : Squarefree L)
    {z H : ℝ} (hH : 0 ≤ H) (hz : 0 < z) (hsqrt : 2000 ≤ Real.sqrt z)
    (hprimes : ∀ p ∈ L.primeFactors, z ≤ (p : ℝ))
    (hLsize : (L : ℝ) ≤ Real.exp (H/50))
    (hcut : cutoffFourierBound^2 ≤ Real.exp (H/10))
    (hK : (L.primeFactors.card : ℝ) ≤ H/10) :
    (positiveArrayEnvelope L (1/16) 1)^2 ≤ Real.exp (H/2) := by
  let k := L.primeFactors.card
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hweight : (1+(1/16 : ℝ))^(2*k) ≤ Real.exp ((k : ℝ)/8) := by
    calc
      _ ≤ (Real.exp (1/16 : ℝ))^(2*k) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1/16 : ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hV : (reciprocalSqrtDivisorSum L)^2 ≤ Real.exp (2*(k : ℝ)/Real.sqrt z) := by
    calc
      _ ≤ (Real.exp ((k : ℝ)/Real.sqrt z))^2 :=
        pow_le_pow_left₀ (reciprocalSqrtDivisorSum_nonneg L)
          (reciprocalSqrtDivisorSum_le_exp hL hz hprimes) 2
      _ = _ := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hden : (2 : ℝ)/Real.sqrt z ≤ 1/1000 := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 2000) hsqrt
    norm_num at hh ⊢
    exact hh
  have he : (k : ℝ)/8+2*(k : ℝ)/Real.sqrt z ≤ (k : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hden hk
    ring_nf at hh ⊢
    nlinarith
  have hprod : (1+(1/16 : ℝ))^(2*k)*(reciprocalSqrtDivisorSum L)^2 ≤ Real.exp (k : ℝ) := by
    calc
      _ ≤ Real.exp ((k : ℝ)/8)*Real.exp (2*(k : ℝ)/Real.sqrt z) :=
        mul_le_mul hweight hV (sq_nonneg _) (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr he
  rw [positiveArrayEnvelope_one_sq]
  calc
    _ = ((L : ℝ)*cutoffFourierBound^2)*
        ((1+(1/16 : ℝ))^(2*k)*(reciprocalSqrtDivisorSum L)^2) := by dsimp [k]; ring
    _ ≤ (Real.exp (H/50)*Real.exp (H/10))*Real.exp (k : ℝ) :=
      mul_le_mul (mul_le_mul hLsize hcut (sq_nonneg _) (Real.exp_pos _).le)
        hprod (mul_nonneg (by positivity) (sq_nonneg _)) (by positivity)
    _ = Real.exp (H/50+H/10+(k : ℝ)) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [k] at *; linarith)

end Ostmann.QuadraticCenter

end

end OAI
