import OAI.NumberTheory.JointDickman.Arithmetic.PrimeMomentNormalized
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! # A sub-square-root sample count from a growing prime moment -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem subsquare_prime_samples : ∀ᶠ X : ℝ in atTop,
    ∀ (M r : ℕ), 2 ≤ M → (M:ℝ)^r ≤ X → X ≤ (M:ℝ)^(r+1) →
      (M:ℝ) ≤ X^(1/100:ℝ) →
      ∀ (P : Finset ℕ) (a : ℕ → ℂ), (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ M) →
      ∀ (T V : ℝ), 0 ≤ T → T ≤ X → 0 < V →
      (r:ℝ)*(∑ p ∈ P, ‖a p‖^2) ≤ (M:ℝ)^(-5/8:ℝ)*V^2 →
      ∀ U : Finset ℝ, (∀ t ∈ U, |t| ≤ T) →
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
      (∀ t ∈ U, V ≤ ‖mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ)) t‖) →
      (U.card:ℝ) ≤ X^(5/12:ℝ) := by
  have hlim : Tendsto (fun X : ℝ => 72*Real.exp 1*(Real.log X)^2/X^(17/480:ℝ))
      atTop (𝓝 0) := by
    have hh := (log_power_div_power_tendsto_zero 2 (by norm_num : (0:ℝ)<17/480)).const_mul
      (72*Real.exp 1)
    simpa only [Real.rpow_ofNat,mul_zero,mul_div_assoc] using hh
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with X hX hbudget
  intro M r hM hMX hXM hscale P a hP ha T V hT hTX hV hmass U hU hsep hlarge
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hX
  have hlog : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hM0 : 0 < (M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hM1 : 1 ≤ (M:ℝ) := by exact_mod_cast (show 1≤M by omega)
  have hp1 : 1 ≤ (M:ℝ)^r := one_le_pow₀ hM1
  have hlogM : 0 ≤ Real.log ((M:ℝ)^r) := Real.log_nonneg hp1
  have hlogMX : Real.log ((M:ℝ)^r) ≤ Real.log X :=
    Real.log_le_log (by positivity) hMX
  have hs : 2+(Real.log ((M:ℝ)^r))^2 ≤ 3*(Real.log X)^2 := by
    nlinarith [pow_le_pow_left₀ hlogM hlogMX 2]
  have hquot : X/(M:ℝ) ≤ (M:ℝ)^r := by
    apply (div_le_iff₀ hM0).mpr
    simpa only [pow_succ] using hXM
  have hdecay : ((M:ℝ)^(-5/8:ℝ))^r ≤ X^(-99/160:ℝ) := by
    rw [Real.rpow_pow_comm hM0.le]
    calc
      _ ≤ (X/(M:ℝ))^(-5/8:ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hquot (by norm_num)
      _ = X^(-5/8:ℝ)*(M:ℝ)^(5/8:ℝ) := by
        rw [Real.div_rpow hX0.le hM0.le,div_eq_mul_inv,← Real.rpow_neg hM0.le]
        norm_num
      _ ≤ X^(-5/8:ℝ)*(X^(1/100:ℝ))^(5/8:ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM0.le hscale (by norm_num)) (by positivity)
      _ = _ := by rw [← Real.rpow_mul hX0.le,← Real.rpow_add hX0]; norm_num
  have hh := mrt_prime_large_values_geometric P a M r hP ha U hT hV hmass hU hsep hlarge
  simp only [Nat.cast_pow] at hh
  apply hh.trans
  calc
    _ ≤ (8*Real.exp 1*(3*X)*(3*(Real.log X)^2))*X^(-99/160:ℝ) := by
      gcongr
      linarith
    _ = (72*Real.exp 1*(Real.log X)^2/X^(17/480:ℝ))*X^(5/12:ℝ) := by
      have hd : (72*Real.exp 1*(Real.log X)^2/X^(17/480:ℝ)) =
          (72*Real.exp 1*(Real.log X)^2)*X^(-17/480:ℝ) := by
        rw [show (-17/480:ℝ)= -(17/480:ℝ) by ring,Real.rpow_neg hX0.le]
        rfl
      rw [hd]
      have he : X*X^(-99/160:ℝ)=X^(-17/480:ℝ)*X^(5/12:ℝ) := by
        conv_lhs => lhs; rw [← Real.rpow_one X]
        rw [← Real.rpow_add hX0,← Real.rpow_add hX0]
        norm_num
      linear_combination (norm := ring_nf) (72*Real.exp 1*(Real.log X)^2)*he
    _ ≤ X^(5/12:ℝ) := mul_le_of_le_one_left (by positivity) hbudget

end JointDickman

end OAI
