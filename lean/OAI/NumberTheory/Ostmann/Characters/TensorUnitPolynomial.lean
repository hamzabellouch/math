import OAI.NumberTheory.Ostmann.Characters.TensorUnitMean
import OAI.NumberTheory.Ostmann.Supply.ElementaryPolynomial

namespace OAI

/-! # Truncating the independent unit-residue mean -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tensorUnitCoefficient {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (E : ∀ i, Finset (ZMod (p i))) (j k : ℕ) : ℂ :=
  tensorUnitMean p (fun x =>
    elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) j *
      elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) k)

theorem tensorUnitCoefficient_polynomial {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (E : ∀ i, Finset (ZMod (p i))) (u v : ℂ) :
    finitePolynomial₂ (tensorUnitCoefficient p E) (n + 1) u v =
      tensorUnitMean p (fun x => ∏ i,
        (1 + u * localSparseKernel (E i) (x i)) * (1 + v * localSparseKernel (E i) (x i))) := by
  let C : ℕ → ℕ → (∀ i, ZMod (p i)) → ℂ := fun j k x =>
    elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) j *
      elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) k
  have hm : tensorUnitMeanLinearMap p (finitePolynomial₂ C (n + 1) u v) =
      finitePolynomial₂ (tensorUnitCoefficient p E) (n + 1) u v := by
    simp only [finitePolynomial₂, finitePolynomial, map_sum, map_smul]
    rfl
  rw [← hm]
  change tensorUnitMean p (finitePolynomial₂ C (n + 1) u v) = _
  apply congrArg (tensorUnitMean p)
  funext x
  have he := elementaryCoefficient_product (fun i => localSparseKernel (E i) (x i)) u v
  simpa only [finitePolynomial₂, finitePolynomial, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, C, Finset.prod_mul_distrib] using he

theorem tensorUnitCoefficient_truncation {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (E : ∀ i, Finset (ZMod (p i))) (K : ℕ) :
    rectangularPolynomialSum (tensorUnitCoefficient p E) (n + 1) K =
      tensorUnitMean p (fun x => elementaryTruncation
        (fun i => localSparseKernel (E i) (x i)) K ^ 2) := by
  let C : ℕ → ℕ → (∀ i, ZMod (p i)) → ℂ := fun j k x =>
    elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) j *
      elementaryCoefficient (fun i => localSparseKernel (E i) (x i)) k
  have hm : tensorUnitMeanLinearMap p (rectangularPolynomialSum C (n + 1) K) =
      rectangularPolynomialSum (tensorUnitCoefficient p E) (n + 1) K := by
    unfold rectangularPolynomialSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs
    · rfl
    · exact map_zero _
  rw [← hm]
  change tensorUnitMean p (rectangularPolynomialSum C (n + 1) K) = _
  apply congrArg (tensorUnitMean p)
  funext x
  have he := elementaryTruncation_square (fun i => localSparseKernel (E i) (x i)) K
  simpa only [rectangularPolynomialSum, Finset.sum_apply, ite_apply, Pi.zero_apply, C] using he

theorem tensorUnitMean_truncation_error {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (E : ∀ i, Finset (ZMod (p i)))
    (hE : ∀ i, 0 ∉ E i) (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : ∀ i, ((E i).card : ℝ) ≤ ε * p i)
    (K : ℕ) :
    ‖tensorUnitMean p (fun x => ∏ i, (1 + localSparseKernel (E i) (x i)) ^ 2) -
      tensorUnitMean p (fun x => elementaryTruncation
        (fun i => localSparseKernel (E i) (x i)) K ^ 2)‖ ≤
        2 * Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) * (100 / 103 : ℝ) ^ (K + 1) /
          (1 - 100 / 103) ^ 2 := by
  have hb (u v : ℂ) (hu : ‖u‖ = 103 / 100) (hv : ‖v‖ = 103 / 100) :
      ‖finitePolynomial₂ (tensorUnitCoefficient p E) (n + 1) u v‖ ≤
        Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) := by
    rw [tensorUnitCoefficient_polynomial]
    exact tensorUnitMean_polydisc p E hE hsym ε hε hε1 hc u v hu.le hv.le
  have ht := finitePolynomial₂_truncation_error (tensorUnitCoefficient p E)
    (103 / 100) _ (by norm_num) (Real.exp_pos _).le hb K
  rw [tensorUnitCoefficient_polynomial, tensorUnitCoefficient_truncation] at ht
  simpa only [one_mul, ← pow_two, show (103 / 100 : ℝ)⁻¹ = 100 / 103 by norm_num] using ht

end Ostmann

end OAI
