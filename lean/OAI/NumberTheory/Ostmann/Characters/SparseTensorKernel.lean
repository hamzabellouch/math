import OAI.NumberTheory.Ostmann.Supply.FiniteTensorKernel
import OAI.NumberTheory.Ostmann.Characters.SparseResidueMatrix
import OAI.NumberTheory.Ostmann.Characters.SparseUnitPolydisc

namespace OAI

/-! # The actual sparse tensor kernel of Section 5.3 -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def sparseTensorKernel {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (u v : ℂ) :
    (∀ i, Option (ZMod (p i))) → (∀ i, Option (ZMod (p i))) → ℂ :=
  finiteTensorKernel (fun i => sparseResidueMatrix (S i)
    (largeTransformSpectrum (normalizedResidueTransform (S i))) u v)

theorem product_one_add_le_exp_sum {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ 1 + a i) :
    (∏ i, (1 + a i)) ≤ Real.exp (∑ i, a i) := by
  calc
    _ ≤ ∏ i, Real.exp (a i) := Finset.prod_le_prod₀ (by intro i _; exact ha i)
      (by intro i _; linarith [Real.add_one_le_exp (a i)])
    _ = _ := (Real.exp_sum _ _).symm

theorem sparseTensorKernel_energy_le {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (u v : ℂ) (hu : ‖u‖ ≤ 103 / 100) (hv : ‖v‖ ≤ 103 / 100)
    (f : (∀ i, Option (ZMod (p i))) → ℂ) :
    (∑ x, ‖∑ y, sparseTensorKernel p S u v x y * f y‖ ^ 2) ≤
      Real.exp (3 * ∑ i, (p i : ℝ)⁻¹) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  have hlocal := fun i => sparseResidueMatrix_energy_le (S i) (hS i) (hSp i) (hp i)
    (hlo i) (hhi i) ε hε hεsmall (hL1 i) u v hu hv
  have ht := finiteTensorKernel_energy_le (fun i => Option (ZMod (p i)))
    (fun i => Option (ZMod (p i))) _ (fun i => 1 + 3 / (p i : ℝ)) hlocal f
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (by intro y _; positivity))
  have hprod := product_one_add_le_exp_sum (fun i => 3 / (p i : ℝ))
    (by intro i; positivity)
  rw [show (∑ i, 3 / (p i : ℝ)) = 3 * ∑ i, (p i : ℝ)⁻¹ by
    simp only [div_eq_mul_inv, Finset.mul_sum]] at hprod
  exact pow_le_pow_left₀ (Finset.prod_nonneg (by intro i _; positivity)) hprod 2

/-- The full (untruncated) product has the manuscript's strict exponential contraction. -/
theorem sparseTensorKernel_contraction {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (f : (∀ i, Option (ZMod (p i))) → ℂ) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    (∑ x, ‖∑ y, sparseTensorKernel p S 1 1 x y * f y‖ ^ 2) ≤
      (U * Real.exp (-(8 / 5) * ∑ i, (p i : ℝ)⁻¹)) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  intro U
  let a : Fin n → ℝ := fun i => sparseKernelUnitFactor (p i)
    (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
  have ha (i) : 0 < a i :=
    (local_sparse_kernel_contraction (S i) (hS i) (hSp i) (hp i) (hlo i) (hhi i)
      ε hε hεsmall (hL1 i)).1
  have hd (i) : 0 ≤ 1 - (8 / 5) / (p i : ℝ) := by
    have hpos : (0 : ℝ) < p i := lt_of_lt_of_le (by norm_num) (hp i)
    have hh : (8 / 5 : ℝ) / p i ≤ 1 := (div_le_one hpos).mpr (by linarith [hp i])
    linarith
  have ht := finiteTensorKernel_energy_le (fun i => Option (ZMod (p i)))
    (fun i => Option (ZMod (p i))) _ (fun i => a i * (1 - (8 / 5) / (p i : ℝ)))
    (fun i => sparseResidueMatrix_contraction (S i) (hS i) (hSp i) (hp i)
      (hlo i) (hhi i) ε hε hεsmall (hL1 i)) f
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (by intro y _; positivity))
  apply pow_le_pow_left₀ (Finset.prod_nonneg (by intro i _; exact mul_nonneg (ha i).le (hd i)))
  rw [Finset.prod_mul_distrib]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (by intro i _; exact (ha i).le))
  have he := product_one_add_le_exp_sum (fun i => -(8 / 5) / (p i : ℝ))
    (by intro i; simpa only [neg_div, sub_eq_add_neg] using hd i)
  simpa only [neg_div, ← sub_eq_add_neg, div_eq_mul_inv, neg_mul,
    Finset.sum_neg_distrib, ← Finset.mul_sum] using he

theorem sparseTensorKernel_point_identity {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (a b : ∀ i, ZMod (p i))
    (ha : ∀ i, a i ∈ S i) (hb : ∀ i, b i ∈ Finset.univ \ S i) (u v : ℂ) :
    (∑ x, conj (∏ i, residuePointCoordinates (S i) (a i) (x i)) *
      ∑ y, sparseTensorKernel p S u v x y *
        ∏ i, residuePointCoordinates (Finset.univ \ S i) (b i) (y i)) =
      ∏ i, (1 + u * localSparseKernel
        (largeTransformSpectrum (normalizedResidueTransform (S i))) (a i - b i)) *
        (1 + v * localSparseKernel
          (largeTransformSpectrum (normalizedResidueTransform (S i))) (a i - b i)) := by
  have he := @finiteTensorKernel_pairing (Fin n) inferInstance
    (fun i => Option (ZMod (p i))) (fun i => Option (ZMod (p i))) inferInstance inferInstance
    (fun (i : Fin n) => sparseResidueMatrix (S i)
      (largeTransformSpectrum (normalizedResidueTransform (S i))) u v)
    (fun (i : Fin n) => residuePointCoordinates (S i) (a i))
    (fun (i : Fin n) => residuePointCoordinates (Finset.univ \ S i) (b i))
  unfold sparseTensorKernel
  have hp := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (i : Fin n) _ => sparseResidueMatrix_point_identity (S i)
      (largeTransformSpectrum (normalizedResidueTransform (S i)))
      (a i) (b i) (ha i) (hb i) u v)
  convert he.trans hp using 1
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _
    congr 1
    apply Finset.sum_congr
    · ext y
      simp
    · intro y _
      rfl

end Ostmann

end OAI
