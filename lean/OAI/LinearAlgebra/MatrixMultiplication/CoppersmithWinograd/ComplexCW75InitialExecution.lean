import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCW75Primitive
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialKernelExecution

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation.CW75InitialExecution

open Polynomial
open scoped BigOperators Classical

abbrev Word := CW75Primitive.Word
abbrev Blocks (N : ℕ) := Fin N → Word

def fullSource (N : ℕ) : Tensor ℂ (Blocks N) (Blocks N) (Blocks N) :=
  Tensor.power (Tensor.power CoppersmithWinograd.tensor 3) N

def support {N : ℕ} (x y z : Blocks N) : Prop := fullSource N x y z ≠ 0

theorem support_iff {N : ℕ} (x y z : Blocks N) :
    support x y z ↔ ∀ i j, (x i j).val + (y i j).val + (z i j).val = 2 := by
  simp [support, fullSource, Tensor.power, Finset.prod_ne_zero_iff,
    CWOriginalWords.tensor_ne_zero_iff]

def boundaryPolynomial (x y z : Word) : Polynomial ℂ :=
  ∏ i, CWBoundary.scalingPolynomial (x i) (y i) (z i)

def boundaryNormalized (x y z : Word) : Polynomial ℂ :=
  ∏ i, (C (CWBoundary.tensor (x i) (y i) (z i)) +
    X ^ 2 * C (CWBoundary.deleted (x i) (y i) (z i)))

theorem boundaryPolynomial_factor (x y z : Word) :
    boundaryPolynomial x y z = X ^ 3 * boundaryNormalized x y z := by
  have hp (i : Fin 3) : CWBoundary.scalingPolynomial (x i) (y i) (z i) =
      X * (C (CWBoundary.tensor (x i) (y i) (z i)) +
        X ^ 2 * C (CWBoundary.deleted (x i) (y i) (z i))) := by
    rw [CWBoundary.scalingPolynomial_apply]
    ring
  simp [boundaryPolynomial, boundaryNormalized, hp, Finset.prod_mul_distrib]

theorem boundaryPolynomial_vanishes (x y z : Word) (j : ℕ) (hj : j < 3) :
    (boundaryPolynomial x y z).coeff j = 0 := by
  rw [boundaryPolynomial_factor]
  simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hj, ite_false]

theorem boundaryPolynomial_leading (x y z : Word) :
    (boundaryPolynomial x y z).coeff 3 = CW75Primitive.source x y z := by
  rw [boundaryPolynomial_factor]
  simp [Polynomial.coeff_X_pow_mul', boundaryNormalized,
    Polynomial.coeff_zero_prod, CW75Primitive.source, Tensor.power]

def completionPolynomial (x y z : Word) : Polynomial ℂ :=
  (if CW75Primitive.hasB x then X else 1) *
    (if CW75Primitive.hasC y then X else 1) *
      (if CW75Primitive.allA z then 0 else 1)

private theorem boundary_one (x y z : Fin 3) (h : CWBoundary.tensor x y z ≠ 0) :
    CWBoundary.tensor x y z = 1 := by
  by_cases hd : x = 1 ∧ y = 0 ∧ z = 1
  · simp [CWBoundary.tensor, hd] at h
  · by_cases hs : x.val + y.val + z.val = 2
    · simp [CWBoundary.tensor, CoppersmithWinograd.tensor, hd, hs]
    · simp [CWBoundary.tensor, CoppersmithWinograd.tensor, hd, hs] at h

private theorem boundarySource_one (x y z : Word) (h : CW75Primitive.source x y z ≠ 0) :
    CW75Primitive.source x y z = 1 := by
  unfold CW75Primitive.source Tensor.power
  apply Finset.prod_eq_one
  intro i hi
  exact boundary_one _ _ _ (CW75Primitive.source_factors x y z h i)

theorem retained_coefficient_one (x y z : Word) (h : CW75Primitive.tensor x y z ≠ 0) :
    CW75Primitive.tensor x y z = 1 := by
  by_cases hr : CW75Primitive.retained x y z
  · rw [CW75Primitive.tensor, ite_eq_left hr] at h ⊢
    exact boundarySource_one x y z h
  · simp [CW75Primitive.tensor, hr] at h

private theorem completion_eq (x y z : Word) (h : CW75Primitive.source x y z ≠ 0) :
    completionPolynomial x y z = CW75Primitive.polynomial x y z := by
  have hone := boundarySource_one x y z h
  rw [CW75Primitive.polynomial_apply]
  by_cases hz : CW75Primitive.allA z <;> simp [completionPolynomial, hone, hz]

private theorem source_mul_retained (x y z : Word) :
    CW75Primitive.source x y z * CW75Primitive.tensor x y z =
      CW75Primitive.tensor x y z := by
  by_cases hs : CW75Primitive.source x y z = 0
  · simp [CW75Primitive.tensor, hs]
  · rw [boundarySource_one x y z hs, one_mul]

def leftBlock (x : Word) : Polynomial ℂ :=
  Polynomial.expand ℂ 2 (∏ i, CWBoundary.outerWeight X (x i)) *
    (if CW75Primitive.hasB x then X else 1)

def middleBlock (y : Word) : Polynomial ℂ :=
  Polynomial.expand ℂ 2 (∏ i, CWBoundary.middleWeight X (y i)) *
    (if CW75Primitive.hasC y then X else 1)

def rightBlock (z : Word) : Polynomial ℂ :=
  Polynomial.expand ℂ 2 (∏ i, CWBoundary.outerWeight X (z i)) *
    (if CW75Primitive.allA z then 0 else 1)

def blockKernel (x y z : Word) : Polynomial ℂ := leftBlock x * middleBlock y * rightBlock z

theorem blockKernel_factor (x y z : Word)
    (hs : ∀ i, (x i).val + (y i).val + (z i).val = 2) :
    blockKernel x y z = Polynomial.expand ℂ 2 (boundaryPolynomial x y z) *
      completionPolynomial x y z := by
  have hpoint (i : Fin 3) :
      CWBoundary.outerWeight X (x i) * CWBoundary.middleWeight X (y i) *
        CWBoundary.outerWeight X (z i) = CWBoundary.scalingPolynomial (x i) (y i) (z i) := by
    unfold CWBoundary.scalingPolynomial
    rw [CWBoundary.outerMap, CWBoundary.middleMap, CWBoundary.restrict_diagonal_apply]
    simp [CoppersmithWinograd.tensor, hs i]
  have hprod : (∏ i, CWBoundary.outerWeight X (x i)) *
      (∏ i, CWBoundary.middleWeight X (y i)) * (∏ i, CWBoundary.outerWeight X (z i)) =
      boundaryPolynomial x y z := by
    simp only [boundaryPolynomial, ← hpoint, Finset.prod_mul_distrib]
  calc
    blockKernel x y z = Polynomial.expand ℂ 2
        ((∏ i, CWBoundary.outerWeight X (x i)) *
          (∏ i, CWBoundary.middleWeight X (y i)) * (∏ i, CWBoundary.outerWeight X (z i))) *
        completionPolynomial x y z := by
      simp only [blockKernel, leftBlock, middleBlock, rightBlock, completionPolynomial, map_mul]
      ring
    _ = _ := by rw [hprod]

theorem blockKernel_vanishes (x y z : Word)
    (hs : ∀ i, (x i).val + (y i).val + (z i).val = 2)
    (j : ℕ) (hj : j < 7) : (blockKernel x y z).coeff j = 0 := by
  rw [blockKernel_factor x y z hs]
  apply PolynomialControlledKernel.expanded_mul_vanishes_of_leading_support
    (boundaryPolynomial x y z) (completionPolynomial x y z) 3 1
    (CW75Primitive.source x y z)
    (boundaryPolynomial_vanishes x y z) (boundaryPolynomial_leading x y z) _ j hj
  intro hn k hk
  rw [completion_eq x y z hn]
  have hkzero : k = 0 := by omega
  subst k
  simp [CW75Primitive.polynomial_coeff]

theorem blockKernel_leading (x y z : Word)
    (hs : ∀ i, (x i).val + (y i).val + (z i).val = 2) :
    (blockKernel x y z).coeff 7 = CW75Primitive.tensor x y z := by
  rw [blockKernel_factor x y z hs]
  have h := PolynomialControlledKernel.expanded_mul_leading_of_leading_support
    (boundaryPolynomial x y z) (completionPolynomial x y z) 3 1
    (CW75Primitive.source x y z) (CW75Primitive.tensor x y z)
    (boundaryPolynomial_vanishes x y z) (boundaryPolynomial_leading x y z) (by
      intro hn
      rw [completion_eq x y z hn]
      simp [CW75Primitive.polynomial_coeff])
  exact h.trans (source_mul_retained x y z)

private theorem degree_product {n D : ℕ} (f : Fin n → Polynomial ℂ)
    (h : ∀ i, (f i).degree ≤ D) : (∏ i, f i).degree ≤ D * n := by
  apply Polynomial.degree_le_of_natDegree_le
  calc
    (∏ i, f i).natDegree ≤ ∑ i, (f i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin n, D := by
      apply Finset.sum_le_sum
      intro i hi
      exact Polynomial.natDegree_le_of_degree_le (h i)
    _ = D * n := by simp [Nat.mul_comm]

private theorem degree_expanded_product (P Q : Polynomial ℂ) {d e : ℕ}
    (hP : P.degree ≤ d) (hQ : Q.degree ≤ e) :
    (Polynomial.expand ℂ 2 P * Q).degree ≤ d * 2 + e := by
  apply Polynomial.degree_le_of_natDegree_le
  apply Polynomial.natDegree_mul_le_of_le
  · rw [Polynomial.natDegree_expand]
    exact Nat.mul_le_mul_right 2 (Polynomial.natDegree_le_of_degree_le hP)
  · exact Polynomial.natDegree_le_of_degree_le hQ

private theorem outerWeight_degree (a : Fin 3) :
    (CWBoundary.outerWeight (X : Polynomial ℂ) a).degree ≤ 1 := by
  by_cases h : a = 1 <;> simp [CWBoundary.outerWeight, h]

private theorem middleWeight_degree (a : Fin 3) :
    (CWBoundary.middleWeight (X : Polynomial ℂ) a).degree ≤ 1 := by
  by_cases h : a = 1 <;> simp [CWBoundary.middleWeight, h]

theorem leftBlock_degree (x : Word) : (leftBlock x).degree ≤ 7 := by
  apply degree_expanded_product (d := 3) (e := 1)
    (∏ i, CWBoundary.outerWeight X (x i)) (if CW75Primitive.hasB x then X else 1)
    (degree_product _ (fun i => outerWeight_degree (x i)))
  by_cases h : CW75Primitive.hasB x <;> simp [h]

theorem middleBlock_degree (y : Word) : (middleBlock y).degree ≤ 7 := by
  apply degree_expanded_product (d := 3) (e := 1)
    (∏ i, CWBoundary.middleWeight X (y i)) (if CW75Primitive.hasC y then X else 1)
    (degree_product _ (fun i => middleWeight_degree (y i)))
  by_cases h : CW75Primitive.hasC y <;> simp [h]

theorem rightBlock_degree (z : Word) : (rightBlock z).degree ≤ 6 := by
  apply degree_expanded_product (d := 3) (e := 0)
    (∏ i, CWBoundary.outerWeight X (z i)) (if CW75Primitive.allA z then 0 else 1)
    (degree_product _ (fun i => outerWeight_degree (z i)))
  by_cases h : CW75Primitive.allA z <;> simp [h]

def auxiliary : Tensor ℂ PUnit.{1} PUnit.{1} PUnit.{1} := fun _ _ _ => 1

theorem auxiliary_rank : Tensor.RankAtMost auxiliary 1 := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_⟩
  funext x y z
  simp [auxiliary, Tensor.rankOne]

def leftMap {N : ℕ} (x : Blocks N) (_ : PUnit.{1} × PUnit.{1}) (_ : PUnit.{1}) : Polynomial ℂ :=
  ∏ i, leftBlock (x i)

def middleMap {N : ℕ} (y : Blocks N) (_ : PUnit.{1} × PUnit.{1}) (_ : PUnit.{1}) : Polynomial ℂ :=
  ∏ i, middleBlock (y i)

def rightMap {N : ℕ} (z : Blocks N) (_ : PUnit.{1} × PUnit.{1}) (_ : PUnit.{1}) : Polynomial ℂ :=
  ∏ i, rightBlock (z i)

def value {N : ℕ} : Tensor ℂ (Blocks N × (PUnit.{1} × PUnit.{1}))
    (Blocks N × (PUnit.{1} × PUnit.{1})) (Blocks N × (PUnit.{1} × PUnit.{1})) :=
  fun x y z => ∏ i, CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i)

theorem kernel_eq {N : ℕ} (x y z : Blocks N × (PUnit.{1} × PUnit.{1})) :
    PolynomialLocalConstruction.kernel auxiliary leftMap middleMap rightMap x y z =
      ∏ i, blockKernel (x.1 i) (y.1 i) (z.1 i) := by
  simp [PolynomialLocalConstruction.kernel, LocalMaps.fiberTransform,
    auxiliary, leftMap, middleMap, rightMap, blockKernel, Finset.prod_mul_distrib]

theorem kernel_coefficients {N : ℕ} (x y z : Blocks N × (PUnit.{1} × PUnit.{1}))
    (hs : support x.1 y.1 z.1) :
    (∀ j, j < 7 * N →
      (PolynomialLocalConstruction.kernel auxiliary leftMap middleMap rightMap x y z).coeff j = 0) ∧
    (PolynomialLocalConstruction.kernel auxiliary leftMap middleMap rightMap x y z).coeff (7 * N) =
      value x y z := by
  have hsites := (support_iff x.1 y.1 z.1).mp hs
  have hd (i : Fin N) : X ^ 7 ∣ blockKernel (x.1 i) (y.1 i) (z.1 i) :=
    Polynomial.X_pow_dvd_iff.mpr (blockKernel_vanishes _ _ _ (hsites i))
  let Q : Fin N → Polynomial ℂ := fun i => Classical.choose (hd i)
  have hQ (i : Fin N) : blockKernel (x.1 i) (y.1 i) (z.1 i) = X ^ 7 * Q i :=
    Classical.choose_spec (hd i)
  have hQzero (i : Fin N) : (Q i).coeff 0 = CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i) := by
    have h := blockKernel_leading _ _ _ (hsites i)
    rw [hQ] at h
    simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] using h
  have hfactor : (∏ i, blockKernel (x.1 i) (y.1 i) (z.1 i)) =
      X ^ (7 * N) * ∏ i, Q i := by
    simp only [hQ, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← pow_mul]
  simp only [kernel_eq, hfactor]
  constructor
  · intro j hj
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hj, ite_false]
  · simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      Polynomial.coeff_zero_prod, hQzero, value]

def execution (N : ℕ) : PolynomialKernelExecution.Execution
    (Blocks N) (Blocks N) (Blocks N) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} support where
  auxiliary := auxiliary
  rankBound := 1
  auxiliary_rank := auxiliary_rank
  order := 7 * N
  leftDegree := 7 * N
  middleDegree := 7 * N
  rightDegree := 6 * N
  leftMap := leftMap
  middleMap := middleMap
  rightMap := rightMap
  left_degree := fun x _ _ => degree_product _ (fun i => leftBlock_degree (x i))
  middle_degree := fun y _ _ => degree_product _ (fun i => middleBlock_degree (y i))
  right_degree := fun z _ _ => degree_product _ (fun i => rightBlock_degree (z i))
  value := value
  vanishes := fun x y z hs => (kernel_coefficients x y z hs).1
  leading := fun x y z hs => (kernel_coefficients x y z hs).2
  synchronized := fun _ _ _ _ _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

@[simp] theorem execution_value (N : ℕ) : (execution N).value = value := rfl

theorem value_ne_zero_iff {N : ℕ} (x y z : Blocks N × (PUnit.{1} × PUnit.{1})) :
    (execution N).value x y z ≠ 0 ↔
      ∀ i, CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i) ≠ 0 := by
  simp [execution_value, value, Finset.prod_ne_zero_iff]

theorem value_retained {N : ℕ} (x y z : Blocks N × (PUnit.{1} × PUnit.{1})) :
    (execution N).value x y z =
      if ∀ i, CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i) ≠ 0 then 1 else 0 := by
  by_cases h : ∀ i, CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i) ≠ 0
  · simp only [ite_eq_left h, execution_value, value]
    apply Finset.prod_eq_one
    intro i hi
    exact retained_coefficient_one _ _ _ (h i)
  · rw [ite_eq_right h]
    by_contra hn
    exact h ((value_ne_zero_iff x y z).mp hn)

end MatrixMultiplication.Foundation.CW75InitialExecution

end

end OAI
