import OAI.NumberTheory.JointDickman.Arithmetic.PrimeMomentNormalized
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! # The auxiliary prime polynomial has only sparsely many large samples -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem auxiliary_large_samples (B : ℝ) (_hB : 1 ≤ B) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ a : ℝ in atTop, ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ f : ℕ → ℂ, OneBounded f → ∀ U : Finset ℝ,
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
      (∀ t ∈ U, |t| ≤ a^B) →
      (((U.filter (fun t => ((Real.log a)^10)⁻¹ <
        ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
          (fun p => -Real.log (p:ℝ)) t‖)).card):ℝ) ≤ a^γ := by
  let r := ⌈B⌉₊
  obtain ⟨C,hC,hbound⟩ := fixed_prime_moment_large_bound r
  let k : ℕ := 2+10*(2*r)
  have hlim : Tendsto (fun a : ℝ => C*(Real.log a)^k/a^γ) atTop (𝓝 0) := by
    have hh := (log_power_div_power_tendsto_zero (k:ℝ) hγ).const_mul C
    simpa only [Real.rpow_natCast,mul_zero,mul_div_assoc] using hh
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with a ha hsmall
  intro Q hQ f hf U hsep hU
  have ha1 : 1 ≤ a := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans ha
  have hlog : 0 < Real.log a := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    (by simpa using Real.log_le_log (Real.exp_pos 1) ha)
  have hheight : a^B ≤ a^r := by
    have hh := Real.rpow_le_rpow_of_exponent_le ha1 (Nat.le_ceil B)
    simpa only [Real.rpow_natCast] using hh
  let V := ((Real.log a)^10)⁻¹
  let S := U.filter (fun t => V < ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
    (fun p => -Real.log (p:ℝ)) t‖)
  have hh := hbound a ha Q hQ f hf S
    (fun x hx y hy hxy => hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy)
    (fun t ht => (hU t (mem_filter.mp ht).1).trans hheight) V (by dsimp [V]; positivity)
    (fun t ht => (mem_filter.mp ht).2.le)
  have he : C*(Real.log a)^2/V^(2*r) = C*(Real.log a)^k := by
    dsimp [V,k]
    rw [inv_pow,div_inv_eq_mul,mul_assoc,← pow_mul,← pow_add]
  apply hh.trans
  rw [he]
  exact (div_le_one (Real.rpow_pos_of_pos (by linarith : 0<a) γ)).mp hsmall

end JointDickman

end OAI
