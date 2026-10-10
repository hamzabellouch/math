import OAI.NumberTheory.Ostmann.Preliminaries.MertensPrimeBands
import OAI.NumberTheory.Ostmann.Construction.TargetPrimeWords

namespace OAI

/-! # Integral endpoints with the original character product scale -/
namespace Ostmann
open scoped Classical

noncomputable def characterEndpointFactor (k : ℕ) : ℝ := 1000 * (4 : ℝ) ^ k
noncomputable def characterRoundedEndpoint (k : ℕ) (v : ℝ) : ℕ :=
  ⌊Real.exp (characterEndpointFactor k * Real.exp v)⌋₊
noncomputable def characterRoundedTau (k : ℕ) (v : ℝ) : ℝ :=
  Real.log (characterRoundedEndpoint k v : ℝ) / characterEndpointFactor k

theorem characterEndpointFactor_pos (k : ℕ) : 0 < characterEndpointFactor k := by
  unfold characterEndpointFactor
  positivity

theorem character_rounded_endpoint_bounds (k : ℕ) (v U : ℝ) (hv : 2 ≤ v) (hUv : U + 1 ≤ v) :
    let X := characterRoundedEndpoint k v
    let τ := characterRoundedTau k v
    1 ≤ X ∧ (X : ℝ) = Real.exp (characterEndpointFactor k * τ) ∧
      2 ≤ τ ∧ (19 / 20 : ℝ) * Real.exp v ≤ τ ∧ τ ≤ Real.exp v ∧
      U ≤ Real.log τ ∧ Real.log τ ≤ v ∧
      Real.log (Real.log (X : ℝ)) ≤ v + Real.log (characterEndpointFactor k) := by
  intro X τ
  have hC := characterEndpointFactor_pos k
  have hCbig : 1000 ≤ characterEndpointFactor k := by
    have hp : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    unfold characterEndpointFactor
    linarith
  have he : 3 ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
  have hT : 1 ≤ characterEndpointFactor k * Real.exp v := by nlinarith
  have hf := floor_exp_log_bounds (characterEndpointFactor k * Real.exp v) hT
  have hXp : (0 : ℝ) < X := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hf.1
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have htlo : (19 / 20 : ℝ) * Real.exp v ≤ τ := by
    apply (le_div_iff₀ hC).mpr
    have hlow := hf.2.1
    change characterEndpointFactor k * Real.exp v - Real.log 2 ≤ Real.log (X : ℝ) at hlow
    nlinarith only [hlow, hCbig, he, hlog2]
  have hthi : τ ≤ Real.exp v := by
    apply (div_le_iff₀ hC).mpr
    exact hf.2.2.trans_eq (mul_comm _ _)
  have ht2 : 2 ≤ τ := by linarith
  have hτ : 0 < τ := by linarith
  have hidentity : characterEndpointFactor k * τ = Real.log (X : ℝ) := by
    dsimp [τ, characterRoundedTau, X]
    exact mul_div_cancel₀ _ hC.ne'
  have hU : U ≤ Real.log τ := by
    apply (Real.le_log_iff_exp_le hτ).mpr
    have hexp : Real.exp U * Real.exp 1 ≤ Real.exp v := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hUv
    have h2 : 2 * Real.exp U ≤ Real.exp U * Real.exp 1 := by
      nlinarith only [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 : ℝ)) (Real.exp_nonneg U)]
    nlinarith only [hexp, h2, htlo, Real.exp_nonneg v]
  refine ⟨hf.1, ?_, ht2, htlo, hthi, hU, ?_, ?_⟩
  · rw [hidentity, Real.exp_log hXp]
  · exact (Real.log_le_iff_le_exp hτ).mpr hthi
  · have hlogp : 0 < Real.log (X : ℝ) := by rw [← hidentity]; positivity
    apply (Real.log_le_iff_le_exp hlogp).mpr
    rw [Real.exp_add, Real.exp_log hC]
    exact hf.2.2.trans_eq (mul_comm _ _)

/-- The floor perturbation leaves every prime of the entire top shell in
its required original logarithmic word range. -/
theorem character_rounded_top_shell (k : ℕ) (v U : ℝ) (hv : 2 ≤ v) (hUv : U + 1 ≤ v)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ p ∈ loglogShell P v, characterRoundedTau k v ≤ Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ 3 * characterRoundedTau k v := by
  have hb := character_rounded_endpoint_bounds k v U hv hUv
  intro p hp
  have hpp := Finset.mem_filter.mp hp
  have hr := prime_shell_log_bounds v p (hP p hpp.1) hpp.2.1 hpp.2.2
  refine ⟨hb.2.2.2.2.1.trans hr.1.le, ?_⟩
  have he : Real.exp 1 ≤ (57 / 20 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_nonneg v)
  nlinarith only [hr.2, he', hb.2.2.2.1]

theorem character_rounded_anchor_pair (k : ℕ) (v U us : ℝ) (hv : 2 ≤ v)
    (hUv : U + 1 ≤ v) (hus : us + 2 ≤ v) :
    3 * Real.exp us + 3 * Real.exp v ≤ 4 * characterRoundedTau k v := by
  have hb := (character_rounded_endpoint_bounds k v U hv hUv).2.2.2.1
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he2 : 4 ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have he := Real.exp_le_exp.mpr hus
  rw [Real.exp_add] at he
  have hm := mul_le_mul_of_nonneg_left he2 (Real.exp_nonneg us)
  nlinarith only [he, hm, hb, Real.exp_nonneg v]

end Ostmann

end OAI
