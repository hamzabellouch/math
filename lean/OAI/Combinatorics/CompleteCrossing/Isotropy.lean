import OAI.Combinatorics.CompleteCrossing.PairSums
import OAI.Combinatorics.CompleteCrossing.Support

namespace OAI

/-! Isotropic evaluation image and order-pairing identities. -/

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

theorem evalFour_swap_first (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapFirstPair P) = evalFour u x y v P := by
  change aeval ![x, u, y, v] (rename (Equiv.swap (0 : Fin 4) 1) P) = aeval ![u, x, y, v] P
  rw [aeval_rename]
  congr 2
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

theorem evalFour_swap_second (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapSecondPair P) = evalFour x u v y P := by
  change aeval ![x, u, y, v] (rename (Equiv.swap (2 : Fin 4) 3) P) = aeval ![x, u, v, y] P
  rw [aeval_rename]
  congr 2
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

theorem evalFour_fullDifference (x u y v : ℝ) :
    evalFour x u y v fullDifference =
      (x - u) * (y - v) * (x - y) * (x - v) * (u - y) * (u - v) := by
  simp [evalFour, fullDifference, collisionFactor]
  ring

def isotropicTerm {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) (P Q : Poly4)
    (i p k q : Fin n) : ℝ :=
  J i p k q * nodeWeight node i * nodeWeight node p * nodeWeight node k * nodeWeight node q *
    evalFour (node i) (node p) (node k) (node q) fullDifference *
    evalFour (node i) (node p) (node k) (node q) P *
    evalFour (node i) (node p) (node k) (node q) Q

theorem isotropicTerm_first {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hJ : ∀ i p k q, J p i k q = -J i p k q) (P Q : endpointSymmetricSpace s)
    (i p k q : Fin n) :
    isotropicTerm node J P.val Q.val p i k q = isotropicTerm node J P.val Q.val i p k q := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.1
  have hq := ((symmetric_space_membership s Q.val).mp Q.property).2.1
  have hep := evalFour_swap_first P.val (node i) (node p) (node k) (node q)
  have heq := evalFour_swap_first Q.val (node i) (node p) (node k) (node q)
  rw [hp] at hep
  rw [hq] at heq
  unfold isotropicTerm
  rw [hJ i p k q, ← hep, ← heq]
  simp only [evalFour_fullDifference]
  ring

theorem isotropicTerm_second {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hJ : ∀ i p k q, J i p q k = -J i p k q) (P Q : endpointSymmetricSpace s)
    (i p k q : Fin n) :
    isotropicTerm node J P.val Q.val i p q k = isotropicTerm node J P.val Q.val i p k q := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.2
  have hq := ((symmetric_space_membership s Q.val).mp Q.property).2.2
  have hep := evalFour_swap_second P.val (node i) (node p) (node k) (node q)
  have heq := evalFour_swap_second Q.val (node i) (node p) (node k) (node q)
  rw [hp] at hep
  rw [hq] at heq
  unfold isotropicTerm
  rw [hJ i p k q, ← hep, ← heq]
  simp only [evalFour_fullDifference]
  ring

theorem isotropicTerm_vanish {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (P Q : Poly4) (i p k q : Fin n)
    (h : i = p ∨ k = q ∨ i = k ∨ i = q ∨ p = k ∨ p = q ∨ J i p k q = 0) :
    isotropicTerm node J P Q i p k q = 0 := by
  rcases h with h | h | h | h | h | h | h <;>
    simp [isotropicTerm, evalFour_fullDifference, h]

theorem support_sum_eq_upper {n : ℕ} (J : CrossingTensor n)
    (f : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hzero : ∀ i p k q, i = k ∨ i = q ∨ p = k ∨ p = q ∨ J i p k q = 0 → f i p k q = 0) :
    (∑ a : SupportCoord J, f a.val.1.1 a.val.1.2 a.val.2.1 a.val.2.2) =
      upperPairSum (fun i p => upperPairSum (f i p)) := by
  let F (a : (Fin n × Fin n) × (Fin n × Fin n)) := f a.1.1 a.1.2 a.2.1 a.2.2
  change (∑ a : SupportCoord J, F a.val) = _
  rw [Finset.sum_coe_sort (supportedPairs J) F]
  simp only [supportedPairs, Finset.sum_filter, Fintype.sum_prod_type, upperPairSum, F]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  by_cases hip : i < p
  · simp only [hip, true_and, ite_true]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro q _
    by_cases hkq : k < q
    · simp only [hkq, true_and, ite_true]
      by_cases hgood : i ≠ k ∧ i ≠ q ∧ p ≠ k ∧ p ≠ q ∧ J i p k q ≠ 0
      · simp [hgood]
      · have hz : f i p k q = 0 := hzero i p k q (by tauto)
        simp [hz]
    · simp [hkq]
  · simp [hip]

theorem supportBilinear_eq_isotropicSum {n s : ℕ} (node : Fin n → ℝ)
    (J : CrossingTensor n) (P Q : endpointSymmetricSpace s) :
    supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) =
      upperPairSum (fun i p => upperPairSum (isotropicTerm node J P.val Q.val i p)) := by
  calc
    _ = ∑ a : SupportCoord J, isotropicTerm node J P.val Q.val
        a.val.1.1 a.val.1.2 a.val.2.1 a.val.2.2 := by
      simp only [supportBilinear, Matrix.toBilin'_apply, Matrix.diagonal_apply,
        mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      apply Finset.sum_congr rfl
      intro a _
      change evalFour _ _ _ _ P.val * supportDiagonal node J a * evalFour _ _ _ _ Q.val = _
      unfold supportDiagonal isotropicTerm
      ring
    _ = _ := support_sum_eq_upper J _ (fun i p k q h =>
      isotropicTerm_vanish node J P.val Q.val i p k q (Or.inr (Or.inr h)))

theorem isotropic_test_degree {s : ℕ} (hs : 2 ≤ s) (P Q : endpointSymmetricSpace s) :
    P.val * Q.val * fullDifference ∈ box4 (2 * s - 1) := by
  apply (box4_membership _ _).mpr
  intro i
  have hΔ : fullDifference.degreeOf i ≤ 3 := by
    have h := degreeOf_mul_bound
      (degreeOf_mul_bound (degreeOf_difference_bound 0 1 i) (degreeOf_difference_bound 2 3 i))
      (le_of_eq (collision_factor_properties.2.2.2 i))
    fin_cases i <;> norm_num [fullDifference] at h ⊢ <;> exact h
  have hp := ((symmetric_space_membership s P.val).mp P.property).1 i
  have hq := ((symmetric_space_membership s Q.val).mp Q.property).1 i
  exact (degreeOf_mul_bound (degreeOf_mul_bound hp hq) hΔ).trans (by omega)

theorem polynomialTest_isotropic {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hfirst : ∀ i p k q, J p i k q = -J i p k q)
    (hsecond : ∀ i p k q, J i p q k = -J i p k q)
    (P Q : endpointSymmetricSpace s) :
    polynomialTest node J (P.val * Q.val * fullDifference) =
      4 * supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) := by
  rw [supportBilinear_eq_isotropicSum]
  have hterm : polynomialTest node J (P.val * Q.val * fullDifference) =
      ∑ i, ∑ p, ∑ k, ∑ q, isotropicTerm node J P.val Q.val i p k q := by
    unfold polynomialTest
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro q _
    rw [evalFour_mul, evalFour_mul]
    unfold isotropicTerm
    ring
  rw [hterm]
  exact sum_symmetric_quad _ (isotropicTerm_first node J hfirst P Q)
    (isotropicTerm_second node J hsecond P Q)
    (fun i k q => isotropicTerm_vanish node J P.val Q.val i i k q (Or.inl rfl))
    (fun i p k => isotropicTerm_vanish node J P.val Q.val i p k k (Or.inr (Or.inl rfl)))

theorem evaluation_image_isotropic {s : ℕ} (hs : 2 ≤ s) (node : Fin (2 * s + 1) → ℝ)
    (_hnode : Function.Injective node) (J : CrossingTensor (2 * s + 1))
    (_orders : ∀ i : Fin (2 * s + 1), LinearOrder {j : Fin (2 * s + 1) // j ≠ i})
    (_hloopLeft : ∀ i k q, J i i k q = 0)
    (_hloopRight : ∀ i p k, J i p k k = 0)
    (hreverseLeft : ∀ i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀ i p k q, J i p q k = -J i p k q)
    (_hskew : ∀ i p k q, J k q i p = -J i p k q)
    (_hlocal : ∀ i (p q : {j : Fin (2 * s + 1) // j ≠ i}),
      J i p.val i q.val = halfOrder (_orders i) p q)
    (htests : ∀ H ∈ box4 (2 * s - 1), polynomialTest node J H = 0)
    (P Q : endpointSymmetricSpace s) :
    supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) = 0 := by
  have h := htests _ (isotropic_test_degree hs P Q)
  rw [polynomialTest_isotropic node J hreverseLeft hreverseRight P Q] at h
  linarith

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

theorem weightedPairing_diagonal_invariant {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (K L : ι → ι → ℝ) (h : ∀p q, p≠q → K p q=L p q)
    (A B : Poly2) : weightedPairing node K A B=weightedPairing node L A B := by
  unfold weightedPairing
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  by_cases hpq : p=q
  · subst q
    simp
  · rw [h p q hpq]

theorem support_swap_mem {n : ℕ} (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q)
    (a : SupportCoord J) : (a.val.2,a.val.1)∈supportedPairs J := by
  obtain ⟨h01,h23,h02,h03,h12,h13,hJ⟩ := (Finset.mem_filter.mp a.property).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,h23,h01,h02.symm,h12.symm,h03.symm,h13.symm,?_⟩
  rwa [hskew,neg_ne_zero]

def supportEdgeSwap {n : ℕ} (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q) (a : SupportCoord J) : SupportCoord J :=
  ⟨(a.val.2,a.val.1),support_swap_mem J hskew a⟩

theorem supportEdgeSwap_involutive {n : ℕ} (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q) :
    Function.Involutive (supportEdgeSwap J hskew) := fun _ => Subtype.ext rfl

theorem supportEdgeSwap_ne {n : ℕ} (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q) (a : SupportCoord J) :
    supportEdgeSwap J hskew a ≠ a := by
  intro he
  have h02 := (Finset.mem_filter.mp a.property).2.2.2.1
  exact h02 (congrArg (fun a : SupportCoord J => a.val.1.1) he).symm

theorem supportDiagonal_swap {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q) (a : SupportCoord J) :
    supportDiagonal node J (supportEdgeSwap J hskew a) = -supportDiagonal node J a := by
  unfold supportDiagonal supportEdgeSwap
  dsimp only
  rw [hskew]
  simp only [evalFour_fullDifference]
  ring

theorem supportBilinear_symmetric {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (x y : SupportCoord J → ℝ) : supportBilinear node J x y=supportBilinear node J y x := by
  simp only [supportBilinear,Matrix.toBilin'_apply,Matrix.diagonal_apply,
    mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem supportDiagonal_swap_block {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hskew : ∀i p k q, J k q i p = -J i p k q) (a : SupportCoord J) :
    (Matrix.diagonal (supportDiagonal node J)).submatrix
      ![a,supportEdgeSwap J hskew a] ![a,supportEdgeSwap J hskew a] =
      Matrix.diagonal ![supportDiagonal node J a,-supportDiagonal node J a] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix,Matrix.diagonal_apply,supportEdgeSwap_ne,
      Ne.symm (supportEdgeSwap_ne J hskew a),supportDiagonal_swap]

end Paper170

end
end

end OAI
