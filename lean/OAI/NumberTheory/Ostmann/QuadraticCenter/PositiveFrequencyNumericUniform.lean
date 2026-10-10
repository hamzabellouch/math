import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightScaleBudget
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyNumericAbsorb
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyNumericUniformMertens

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology
open Filter

theorem positiveDivisorArray_actual_uniform_energy_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (Z z L q P : ℕ),
      1 ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z → Real.log z ≤ 2*T^auxiliaryExponent →
      Squarefree L → L.primeFactors.card = auxiliaryK Z z →
      (L : ℝ) ≤ (Z : ℝ)^((1 : ℝ)/50) → (∀ p ∈ L.primeFactors, z ≤ p) →
      Z ≤ P →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (R h θ : ℝ), 0 < R →
      (∑ s ∈ (Finset.Icc 1 (Z^14)).filter (fun s => Squarefree s ∧ s.Coprime L),
        (((2*gridMomentParameter T)^2 : ℕ) : ℝ)^s.primeFactors.card *
          ‖positiveDivisorArray L q (1/16) A mInv P R h θ s‖^2) ≤ 1/(Z : ℝ) := by
  obtain ⟨C, hC, hM⟩ := positiveDivisorArray_uniform_energy_mertens
  filter_upwards [eventually_positive_array_euler_cost C,
    eventually_auxiliaryK_le_log (1/10) (by norm_num),
    eventually_grid_dimension_bound, eventually_parameter_Z_pow_bound,
    eventually_quadratic_energy_sqrt_z, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (20*Real.log (cutoffFourierBound^2))] with T hEuler hK huup hBup hsqrt hT hCut
  intro Z z L q P hZ hZl hZu hz hzl hzu hL hLK hLsize hprimes hP A mInv R h θ hR
  have hZ0 : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hZr : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZr
  have hB : 1 ≤ Z^14 := Nat.one_le_pow 14 Z hZ
  let u : ℝ := (((2*gridMomentParameter T)^2 : ℕ) : ℝ)
  have hu : 0 ≤ u := Nat.cast_nonneg _
  have hcut : cutoffFourierBound^2 ≤ Real.exp (Real.log Z/10) := by
    have hh : Real.log (cutoffFourierBound^2) ≤ Real.log Z/10 := by linarith
    simpa only [Real.exp_log (sq_pos_of_pos cutoffFourierBound_pos)] using Real.exp_le_exp.mpr hh
  have hLexp : (L : ℝ) ≤ Real.exp (Real.log Z/50) := by
    simpa only [Real.rpow_def_of_pos hZ0, mul_one_div] using hLsize
  have hk : (L.primeFactors.card : ℝ) ≤ Real.log Z/10 := by
    rw [hLK]
    have hh := hK Z z hZl hZu hz hzl hzu
    nlinarith
  have hEnv := positive_array_envelope_sq_le_exp hL hlogZ hz0 (hsqrt z hz hzl)
    (fun p hp => by exact_mod_cast hprimes p hp) hLexp hcut hk
  have hloglog : Real.log (Real.log (2*((Z^14 : ℕ) : ℝ))) ≤ 3*Real.log T :=
    high_weight_loglog_le hT hB (by exact_mod_cast hBup Z hZ hZu)
  have hEul : u*(Real.log (Real.log (2*((Z^14 : ℕ) : ℝ)))+C) ≤ Real.log Z/10 := by
    exact (mul_le_mul_of_nonneg_left (by linarith [hloglog]) hu).trans
      (hEuler u (Real.log Z) hu huup hZl)
  have hE := hM L q P Z (Z^14) hL hP (by omega) hB
    (1/16) u (by norm_num) hu A mInv R h θ hR
  apply hE.trans
  rw [div_pow]
  calc
    _ ≤ (Real.exp (Real.log Z/2)/(Z : ℝ)^2)*Real.exp (Real.log Z/10) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right hEnv (sq_nonneg _)
      · exact Real.exp_le_exp.mpr hEul
      · exact (Real.exp_pos _).le
      · positivity
    _ = Real.exp (-(7/5 : ℝ)*Real.log Z) := by
      rw [show (Z : ℝ)^2 = Real.exp (2*Real.log Z) by
        rw [show (2 : ℝ)*Real.log Z = Real.log ((Z : ℝ)^2) by rw [Real.log_pow]; norm_num,
          Real.exp_log (sq_pos_of_pos hZ0)], ← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log Z) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg, Real.exp_log hZ0, one_div]

end Ostmann.QuadraticCenter

end

end OAI
