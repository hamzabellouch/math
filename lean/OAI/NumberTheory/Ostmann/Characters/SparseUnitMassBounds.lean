import OAI.NumberTheory.Ostmann.Characters.SparseKernelUnitFactor
import OAI.NumberTheory.Ostmann.Characters.SparseTensorKernel

namespace OAI

/-! # Lower and upper bounds for the full unit normalizer -/

namespace Ostmann
open scoped Classical BigOperators

theorem exp_neg_two_le_one_sub (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hp : 0 < 1 - x := by linarith
  have hi : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hl := Real.one_sub_inv_le_log_of_pos hp
  rw [← Real.exp_log hp]
  exact Real.exp_le_exp.mpr (by linarith)

theorem sparseKernelUnitFactor_upper (p e : ℝ) (hp : 1 < p) (he : 0 ≤ e) :
    sparseKernelUnitFactor p e ≤ 1 := by
  unfold sparseKernelUnitFactor
  have hn : (17 / 20 : ℝ) ^ 2 * (e - e ^ 2) - (17 / 10) * e ≤ 0 := by
    nlinarith [sq_nonneg e]
  have hh := div_nonpos_of_nonpos_of_nonneg hn (show 0 ≤ p - 1 by linarith)
  linarith

theorem sparseKernelUnitFactor_exp_lower (p e ε : ℝ) (hp : 100 ≤ p)
    (he : 0 ≤ e) (heε : e ≤ ε) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000) :
    Real.exp (-8 * ε / p) ≤ sparseKernelUnitFactor p e := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ 4 * ε / p := by positivity
  have hx1 : 4 * ε / p ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hh := exp_neg_two_le_one_sub (4 * ε / p) hx0 hx1
  have hl := sparseKernelUnitFactor_lower p e ε (by linarith) he heε hε (by linarith)
  apply le_trans _ hl
  convert hh using 1
  congr 1
  ring

theorem sparse_unit_mass_range {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (E : ∀ i, Finset (ZMod (p i))) (hp : ∀ i, (100 : ℝ) ≤ p i)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hc : ∀ i, ((E i).card : ℝ) ≤ ε * p i) :
    let U := ∏ i, sparseKernelUnitFactor (p i) (((E i).card : ℝ) / p i)
    Real.exp (-8 * ε * ∑ i, (p i : ℝ)⁻¹) ≤ U ∧ U ≤ 1 := by
  intro U
  have hratio (i : Fin n) : ((E i).card : ℝ) / p i ≤ ε :=
    (div_le_iff₀ (show (0 : ℝ) < p i by linarith [hp i])).mpr (hc i)
  constructor
  · have hh := Finset.prod_le_prod₀ (s := Finset.univ)
      (fun (i : Fin n) _ => (Real.exp_pos (-8 * ε / p i)).le)
      (fun (i : Fin n) _ => sparseKernelUnitFactor_exp_lower (p i) _ ε (hp i)
        (by positivity) (hratio i) hε hεsmall)
    rw [← Real.exp_sum] at hh
    simpa only [U, div_eq_mul_inv, ← Finset.mul_sum] using hh
  · apply Finset.prod_le_one₀
    · intro i _
      exact (sparseKernelUnitFactor_positive (p i) _ ε (hp i) (by positivity)
        (hratio i) hε hεsmall).le
    · intro i _
      exact sparseKernelUnitFactor_upper _ _ (by linarith [hp i]) (by positivity)

end Ostmann

end OAI
