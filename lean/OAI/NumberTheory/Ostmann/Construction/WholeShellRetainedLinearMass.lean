import OAI.NumberTheory.Ostmann.Construction.WholeShellLinearMass
import OAI.NumberTheory.Ostmann.Construction.RetainedPrimeNormalization

namespace OAI

/-! # Linear bulk mass after every allowed finite deletion -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem whole_shell_retained_linear_mass {C : ℝ} (hM : MertensEstimate C)
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp (K * L) →
      L / 16000 ≤ ∑ p ∈ primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D, (p : ℝ)⁻¹ := by
  filter_upwards [whole_shell_linear_mass hM,
    arithmetic_exponent_absorption 0 (4 / 1000) 0 K 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (16000 : ℝ)] with L hmass hrate hL
  intro D hD
  let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
    (Real.exp ((6 / 1000 : ℝ) * L))
  have hL0 : 0 ≤ L := by linarith
  have hlo : ∀ p ∈ S, Real.exp (Real.exp ((4 / 1000 : ℝ) * L)) ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hp, _, hlo, _⟩ := mem_primeLogCellSet_iff.mp hp
    exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mp hlo).le
  have hdel : (∑ p ∈ S ∩ D, (p : ℝ)⁻¹) ≤ 1 := by
    apply (bulk_deleted_reciprocal_mass_le S D _ hlo).trans
    apply (mul_le_mul_of_nonneg_right hD (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply (Real.exp_le_exp.mpr (show K * L + -Real.exp ((4 / 1000 : ℝ) * L) ≤ 0 from ?_)).trans_eq
    · exact Real.exp_zero
    · simp only [zero_mul, Real.exp_zero, mul_one, one_mul, pow_one] at hrate
      nlinarith [mul_nonneg hK hL0]
  have hs := Finset.sum_inter_add_sum_sdiff S D (fun p : ℕ => (p : ℝ)⁻¹)
  change L / 16000 ≤ ∑ p ∈ S \ D, (p : ℝ)⁻¹
  change L / 8000 ≤ ∑ p ∈ S, (p : ℝ)⁻¹ at hmass
  linarith

end Ostmann

end OAI
