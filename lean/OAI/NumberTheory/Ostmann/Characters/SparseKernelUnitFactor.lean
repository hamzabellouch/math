import OAI.NumberTheory.Ostmann.Characters.SparseKernelMeans

namespace OAI

/-! # The unit-residue normalizing factor at the fixed kernel parameter -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparseKernelUnitFactor (p e : ℝ) : ℝ :=
  1 + (((17 / 20 : ℝ) ^ 2) * (e - e ^ 2) - (17 / 10) * e) / (p - 1)

theorem sparseKernelUnitFactor_lower (p e ε : ℝ) (hp : 2 ≤ p)
    (he : 0 ≤ e) (heε : e ≤ ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - 4 * ε / p ≤ sparseKernelUnitFactor p e := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hn : -2 * ε ≤ ((17 / 20 : ℝ) ^ 2) * (e - e ^ 2) - (17 / 10) * e := by
    have he1 : e ≤ 1 := heε.trans hε1
    nlinarith
  have hfrac : -4 * ε / p ≤ -2 * ε / (p - 1) := by
    apply (div_le_div_iff₀ hp0 hp1).mpr
    nlinarith [mul_nonneg hε0 (sub_nonneg.mpr hp)]
  unfold sparseKernelUnitFactor
  calc
    1 - 4 * ε / p = 1 + (-4 * ε / p) := by ring
    _ ≤ 1 + (-2 * ε / (p - 1)) := add_le_add le_rfl hfrac
    _ ≤ _ := add_le_add le_rfl ((div_le_div_iff_of_pos_right hp1).mpr hn)

theorem sparseKernelUnitFactor_positive (p e ε : ℝ) (hp : 100 ≤ p)
    (he : 0 ≤ e) (heε : e ≤ ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 1000000) :
    0 < sparseKernelUnitFactor p e := by
  have hp0 : 0 < p := by linarith
  have hh := sparseKernelUnitFactor_lower p e ε (by linarith) he heε hε0 (by linarith)
  have heps : 4 * ε / p < 1 := (div_lt_one hp0).mpr (by linarith)
  linarith

/-- The closed expression is the actual mean of `(1+b)^2` on nonzero
residues, with `b` the manuscript's fixed `17/20` kernel. -/
theorem sparseKernelUnitFactor_mean {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (hsym : ∀ b, -b ∈ E ↔ b ∈ E)
    (hp : 1 < p) :
    ((sparseKernelUnitFactor p ((E.card : ℝ) / p) : ℝ) : ℂ) =
      ((p : ℂ) - 1)⁻¹ * ∑ x ∈ Finset.univ.erase 0,
        (1 + sparseAdditiveKernel E (17 / 20) x) ^ 2 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne')
  have hc : ((Finset.univ.erase (0 : ZMod p)).card : ℂ) = (p : ℂ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  have he (x : ZMod p) : (1 + sparseAdditiveKernel E (17 / 20) x) ^ 2 =
      1 + 2 * sparseAdditiveKernel E (17 / 20) x +
        sparseAdditiveKernel E (17 / 20) x * sparseAdditiveKernel E (17 / 20) x := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sparseAdditiveKernel_sum_nonzero E hE, sparseAdditiveKernel_square_sum_nonzero E hsym]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hc]
  unfold sparseKernelUnitFactor
  push_cast
  field_simp
  ring

end Ostmann

end OAI
