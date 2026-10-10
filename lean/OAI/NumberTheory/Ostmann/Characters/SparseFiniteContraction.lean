import OAI.NumberTheory.Ostmann.Characters.SparseWeightUnitMean
import OAI.NumberTheory.Ostmann.Characters.SparseTruncatedOperator

namespace OAI

/-! # Completed finite contraction and unit-mass estimates -/

namespace Ostmann
open scoped Classical BigOperators

theorem sparse_normalizer_error_bounds (L H ε U : ℝ)
    (hL : 1 ≤ L) (hH0 : 0 ≤ H) (hH : H ≤ L)
    (hεsmall : ε ≤ 1 / 1000000)
    (hU : Real.exp (-8 * ε * H) ≤ U) :
    0 < U ∧ Real.exp (-5 * L) ≤ U / 2 ∧
      Real.exp (-5 * L) ≤ U * Real.exp (-(8 / 5) * H) := by
  have hcoarse : Real.exp (-L) ≤ U := by
    apply le_trans _ hU
    apply Real.exp_le_exp.mpr
    have hh : 8 * ε * H ≤ H := by
      have he : 8 * ε ≤ 1 := by linarith
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he hH0
    linarith
  have hhalf : Real.exp (-(4 * L)) ≤ 1 / 2 := by
    have he : (2 : ℝ) ≤ Real.exp (4 * L) := by
      linarith [Real.add_one_le_exp (4 * L)]
    rw [Real.exp_neg, ← one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
  refine ⟨(Real.exp_pos _).trans_le hcoarse, ?_, ?_⟩
  · calc
      Real.exp (-5 * L) = Real.exp (-L) * Real.exp (-(4 * L)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ U * (1 / 2) := mul_le_mul hcoarse hhalf (Real.exp_pos _).le
        ((Real.exp_pos _).trans_le hcoarse).le
      _ = U / 2 := by ring
  · calc
      Real.exp (-5 * L) ≤ Real.exp (-L - (8 / 5) * H) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-L) * Real.exp (-(8 / 5) * H) := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]
      _ ≤ U * Real.exp (-(8 / 5) * H) :=
        mul_le_mul_of_nonneg_right hcoarse (Real.exp_pos _).le

/-- The concrete finite output used by Proposition 5.1: the nonnegative
weight keeps a positive unit mean while its pair kernel contracts. -/
theorem sparse_finite_contraction {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (K : ℕ) (hK : 1000 * L ≤ K) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    0 < U ∧ U / 2 ≤ tensorRealUnitMean p (sparseSubsetWeight p S K) ∧
      ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ ≤
        2 * U * Real.exp (-(8 / 5) * ∑ i, (p i : ℝ)⁻¹) := by
  intro U
  let H := ∑ i, (p i : ℝ)⁻¹
  let E := fun i => largeTransformSpectrum (normalizedResidueTransform (S i))
  have hs (i : Fin n) := normalizedResidueTransform_sparse (S i) (hS i) (hSp i)
    ε (ε ^ 2) (by nlinarith) le_rfl (hL1 i)
  have hU := (sparse_unit_mass_range p E hp ε hε hεsmall (fun i => (hs i).2.2.1)).1
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun i _ => by positivity)
  obtain ⟨hpos, hehalf, heratio⟩ := sparse_normalizer_error_bounds L H ε U hL hH0 hH hεsmall hU
  refine ⟨hpos, ?_, ?_⟩
  · have hm := sparseWeightUnitMean_close p S hS hSp ε hε hεsmall hL1 L hL hH K hK
    have hh := (abs_le.mp hm).1
    linarith
  · have ht := truncatedSparseTensorKernel_norm_le p S hS hSp hp hlo hhi ε hε hεsmall hL1 K
    have he := sparse_truncation_error_rate L (H / 2) K hL (by dsimp [H]; linarith) hK
    rw [show 6 * (H / 2) = 3 * H by ring] at he
    have herr := he.trans heratio
    change ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ ≤
      U * Real.exp (-(8 / 5) * H) +
        2 * Real.exp (3 * H) * (100 / 103 : ℝ) ^ (K + 1) / (1 - 100 / 103) ^ 2 at ht
    linarith

end Ostmann

end OAI
