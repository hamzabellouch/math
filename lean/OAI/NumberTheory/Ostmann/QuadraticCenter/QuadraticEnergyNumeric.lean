import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyNumericScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology
open Filter

theorem positiveDivisorArray_actual_large_energy_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (Z z L q : ℕ),
      1 ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z → Real.log z ≤ 2*T^auxiliaryExponent →
      Squarefree L → 2 ≤ L → L.primeFactors.card = auxiliaryK Z z →
      (L : ℝ) ≤ (Z : ℝ)^((1 : ℝ)/50) → (∀ p ∈ L.primeFactors, z ≤ p) →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (R h θ : ℝ), 0 < R →
      (∑ s ∈ (Finset.Icc (L^4) (Z^14)).filter (fun s => Squarefree s ∧ s.Coprime L),
        (((2*gridMomentParameter T)^2 : ℕ) : ℝ)^s.primeFactors.card *
          ‖positiveDivisorArray L q (1/16) A mInv 1 R h θ s‖^2) ≤
      Real.exp ((12/1000 : ℝ)*(auxiliaryK Z z : ℝ)) := by
  let C := quadraticCorrelationConstant+cutoffFourierBound^2
  have hC : 0 < C := add_pos_of_pos_of_nonneg quadraticCorrelationConstant_pos (sq_nonneg _)
  filter_upwards [positiveDivisorArray_large_energy_log_eventually,
    eventually_auxiliaryK_bounds, eventually_grid_dimension_bound,
    eventually_quadratic_energy_sqrt_z,
    eventually_linear_cost_le_exp_K (100*C) (1/500) (by positivity) (by norm_num),
    eventually_ge_atTop (40 : ℝ)] with T henergy hK huup hsqrt hcost hT
  intro Z z L q hZ hZl hZu hz hzl hzu hL hL2 hLK hLsize hprimes A mInv R h θ hR
  have hT1 : 1 ≤ T := by linarith
  have hKlow := (hK Z z hZl hZu hz hzl hzu).1
  have hZ0 : 0 < Z := by omega
  have hN := quadratic_energy_log_count_le hT1 hZu
  have hcost' : (((Nat.log 2 (Z^14)+1 : ℕ) : ℝ))*C ≤ Real.exp ((auxiliaryK Z z : ℝ)/500) := by
    calc
      _ ≤ (100*C)*T := by nlinarith
      _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hcost (auxiliaryK Z z) hKlow
  have he := henergy L (Z^14) q hL hL2 (pow_pos hZ0 14)
    (quadratic_energy_cutoff_bound hT hZ hZu hLsize)
    (((2*gridMomentParameter T)^2 : ℕ) : ℝ) (auxiliaryK Z z) (1/16) z
    (quadratic_energy_grid_weight_gt_one hT1) huup hKlow (by norm_num)
    (by exact_mod_cast hz : (0 : ℝ) < z)
    (fun p hp => by exact_mod_cast hprimes p hp) A mInv R h θ hR
  rw [hLK] at he
  exact he.trans (quadratic_large_energy_numeric_absorb (auxiliaryK Z z)
    (Nat.cast_nonneg _) (hsqrt z hz hzl) hcost')

end Ostmann.QuadraticCenter

end

end OAI
