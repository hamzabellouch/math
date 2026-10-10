import OAI.Combinatorics.CompleteCrossing.AlgebraDefs
import OAI.Combinatorics.Crossing.TwoTriangleUnisolvence
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace OAI

/-! Bivariate interpolation degrees, spaces, pairings, and polynomial tests. -/

section

/-! Degree conventions and interpolation weights.
 -/

open scoped BigOperators
noncomputable section

namespace Paper170

theorem rectangle_membership (a b : ℕ) (P : Poly2) :
    P ∈ rectangle a b ↔ P.degreeOf 0 ≤ a ∧ P.degreeOf 1 ≤ b := by
  change P.degrees ≤ _ ↔ _
  rw [Multiset.le_iff_count]
  simp [← MvPolynomial.degreeOf_def, Fin.forall_fin_two, Multiset.count_replicate]

theorem box4_membership (d : ℕ) (P : Poly4) :
    P ∈ box4 d ↔ ∀ i, P.degreeOf i ≤ d := by
  change P.degrees ≤ _ ↔ _
  rw [Multiset.le_iff_count]
  simp [← MvPolynomial.degreeOf_def]

theorem symmetric_space_membership (s : ℕ) (P : Poly4) :
    P ∈ endpointSymmetricSpace s ↔
      (∀ i, P.degreeOf i ≤ s - 2) ∧ swapFirstPair P = P ∧ swapSecondPair P = P := by
  simp [endpointSymmetricSpace, box4_membership, sub_eq_zero, and_assoc]

theorem derivative_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (i : ι) :
    Zarankiewicz.derivativeAtNode node i = ∏ j ∈ Finset.univ.erase i, (node i - node j) :=
  Zarankiewicz.derivativeAtNode_eq_prod node i

theorem weight_nonzero {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (hn : Function.Injective node) (i : ι) : nodeWeight node i ≠ 0 := by
  classical
  exact inv_ne_zero (Zarankiewicz.derivativeAtNode_ne_zero node hn i)

theorem interpolation_weights {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (hn : Function.Injective node) (A : Polynomial ℝ)
    (hA : A.degree < (Fintype.card ι - 1 : ℕ)) :
    (∑ i, A.eval (node i) / Zarankiewicz.derivativeAtNode node i) = 0 := by
  classical
  exact Zarankiewicz.node_polynomial_moment node hn A hA

theorem omitted_node_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (hn : Function.Injective node) (i p : ι) (hip : i ≠ p) :
    (node p - node i) * nodeWeight node p =
      ((omittedNodePolynomial node i).derivative.eval (node p))⁻¹ := by
  have hF : Zarankiewicz.nodePolynomial node =
      (Polynomial.X - Polynomial.C (node i)) * omittedNodePolynomial node i :=
    Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)
  have hzero : (omittedNodePolynomial node i).eval (node p) = 0 :=
    Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨hip.symm, Finset.mem_univ p⟩)
  have hd : Zarankiewicz.derivativeAtNode node p = (node p - node i) *
      (omittedNodePolynomial node i).derivative.eval (node p) := by
    rw [Zarankiewicz.derivativeAtNode, hF, Polynomial.derivative_mul]
    simp [hzero]
  have hdiff : node p - node i ≠ 0 := sub_ne_zero.mpr (hn.ne hip.symm)
  rw [nodeWeight, hd, mul_inv, ← mul_assoc, mul_inv_cancel₀ hdiff, one_mul]

theorem weighted_chain_boundary {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (a b : ℕ) (ha : a + 1 < n) (hb : b + 1 < n) :
    ∀ v, chainBoundary (weightedChain node a b) v = 0 := by
  have hsum (k : ℕ) (hk : k + 1 < n) : ∑ i, nodeWeight node i * node i ^ k = 0 := by
    simpa only [nodeWeight, div_eq_mul_inv, mul_comm] using
      Zarankiewicz.node_power_moment node hn k (by simpa using hk)
  have hz (i p : Fin n) : weightedChain node a b i p =
      (nodeWeight node i * node i ^ a) * (nodeWeight node p * node p ^ b) := by
    unfold weightedChain
    ring
  intro v
  simp only [chainBoundary, hz, ← Finset.sum_mul, ← Finset.mul_sum, hsum a ha, hsum b hb,
    zero_mul, mul_zero, sub_self]

end Paper170

end
end

section

/-! Separate degree bounds for the local four-variable test polynomial. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem degreeOf_mul_bound {i : Fin 4} {P Q : Poly4} {a b : ℕ}
    (hP : P.degreeOf i ≤ a) (hQ : Q.degreeOf i ≤ b) : (P*Q).degreeOf i ≤ a+b :=
  (MvPolynomial.degreeOf_mul_le i P Q).trans (Nat.add_le_add hP hQ)

theorem degreeOf_liftUnivariate (i k : Fin 4) (U : Polynomial ℝ) :
    (liftUnivariate i U).degreeOf k ≤ if k=i then U.natDegree else 0 := by
  classical
  unfold liftUnivariate
  conv_lhs => rw [← Polynomial.sum_monomial_eq U, Polynomial.sum, map_sum]
  apply (MvPolynomial.degreeOf_sum_le k _ _).trans
  apply Finset.sup_le
  intro a ha
  rw [Polynomial.aeval_monomial]
  change (MvPolynomial.C (U.coeff a) * MvPolynomial.X i ^ a).degreeOf k ≤ _
  apply (MvPolynomial.degreeOf_C_mul_le _ k _).trans
  by_cases h : k=i
  · subst k
    simpa using Polynomial.le_natDegree_of_mem_supp a ha
  · simp only [ite_eq_right h, MvPolynomial.degreeOf_X_pow_of_ne a h]
    exact Nat.le_refl 0

theorem liftBivariate_eq_rename (i j : Fin 4) (B : Poly2) :
    liftBivariate i j B = MvPolynomial.rename ![i,j] B := by
  have hf : (MvPolynomial.X ∘ (![i,j] : Fin 2 → Fin 4)) =
      (![MvPolynomial.X i, MvPolynomial.X j] : Fin 2 → Poly4) := by
    funext k
    fin_cases k <;> rfl
  simp only [liftBivariate, MvPolynomial.rename_eq_aeval, hf]

theorem degreeOf_rename_zero {σ : Type*} (f : σ → Fin 4) (B : MvPolynomial σ ℝ)
    (k : Fin 4) (hk : ∀i, f i ≠ k) : (MvPolynomial.rename f B).degreeOf k = 0 := by
  by_contra h
  obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename f B
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr h)
  exact hk i hi

theorem degreeOf_liftBivariate13 (B : Poly2) (k : Fin 4) :
    (liftBivariate 1 3 B).degreeOf k = ![0,B.degreeOf 0,0,B.degreeOf 1] k := by
  have hi : Function.Injective (![1,3] : Fin 2 → Fin 4) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢
  rw [liftBivariate_eq_rename]
  fin_cases k
  · exact degreeOf_rename_zero _ B 0 (by intro i; fin_cases i <;> decide)
  · exact MvPolynomial.degreeOf_rename_of_injective hi 0
  · exact degreeOf_rename_zero _ B 2 (by intro i; fin_cases i <;> decide)
  · exact MvPolynomial.degreeOf_rename_of_injective hi 1

theorem degreeOf_difference_bound (i j k : Fin 4) :
    (MvPolynomial.X i - MvPolynomial.X j : Poly4).degreeOf k ≤
      max (if k=i then 1 else 0) (if k=j then 1 else 0) := by
  simpa only [MvPolynomial.degreeOf_X] using
    MvPolynomial.degreeOf_sub_le k (MvPolynomial.X i : Poly4) (MvPolynomial.X j)

theorem local_test_degree (s : ℕ) (hs : 2 ≤ s) (P : Poly4)
    (hP : P ∈ endpointSymmetricSpace s) (U V : Polynomial ℝ)
    (hU : U.natDegree ≤ s) (hV : V.natDegree ≤ s) (B : Poly2)
    (hB : B ∈ rectangle (s-1) (s-1)) :
    localTestPolynomial P U V B ∈ box4 (2*s-1) := by
  apply (box4_membership _ _).mpr
  intro k
  have hP := ((symmetric_space_membership s P).mp hP).1 k
  have hB := (rectangle_membership _ _ B).mp hB
  have h := degreeOf_mul_bound
    (degreeOf_mul_bound
      (degreeOf_mul_bound
        (degreeOf_mul_bound
          (degreeOf_mul_bound
            (degreeOf_mul_bound hP (degreeOf_difference_bound 1 3 k))
            (degreeOf_difference_bound 1 2 k))
          (degreeOf_difference_bound 3 0 k))
        (degreeOf_liftUnivariate 0 k U))
      (degreeOf_liftUnivariate 2 k V))
    (Nat.le_of_eq (degreeOf_liftBivariate13 B k))
  change (localTestPolynomial P U V B).degreeOf k ≤ _ at h
  fin_cases k <;> norm_num [Fin.ext_iff] at h ⊢ <;> omega

end Paper170

end
end

section

/-! Interpolation moments remove row and column perturbations from the order pairing. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem evalTwo_monomial (u v : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    evalTwo u v (MvPolynomial.monomial m c) = c*(u^m 0*v^m 1) := by
  simp only [evalTwo, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
    Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two]
  · intro i
    simp

theorem weighted_evalTwo_second_zero {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (hn : Function.Injective node) (u : ℝ) (P : Poly2)
    (hP : P.degreeOf 1 + 1 < Fintype.card ι) :
    (∑q, evalTwo u (node q) P / Zarankiewicz.derivativeAtNode node q) = 0 := by
  classical
  rw [P.as_sum]
  simp only [map_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  have hmdeg := MvPolynomial.le_degreeOf_of_mem_support 1 hm
  have hz := Zarankiewicz.node_power_moment node hn (m 1) (by omega)
  calc
    (∑q, evalTwo u (node q) (MvPolynomial.monomial m (P.coeff m)) /
        Zarankiewicz.derivativeAtNode node q) =
      (P.coeff m*u^m 0) * ∑q, node q^m 1 / Zarankiewicz.derivativeAtNode node q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [evalTwo_monomial]
      ring
    _ = 0 := by rw [hz,mul_zero]

theorem weighted_evalTwo_first_zero {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (hn : Function.Injective node) (v : ℝ) (P : Poly2)
    (hP : P.degreeOf 0 + 1 < Fintype.card ι) :
    (∑p, evalTwo (node p) v P / Zarankiewicz.derivativeAtNode node p) = 0 := by
  classical
  rw [P.as_sum]
  simp only [map_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  have hmdeg := MvPolynomial.le_degreeOf_of_mem_support 0 hm
  have hz := Zarankiewicz.node_power_moment node hn (m 0) (by omega)
  calc
    (∑p, evalTwo (node p) v (MvPolynomial.monomial m (P.coeff m)) /
        Zarankiewicz.derivativeAtNode node p) =
      (P.coeff m*v^m 1) * ∑p, node p^m 0 / Zarankiewicz.derivativeAtNode node p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [evalTwo_monomial]
      ring
    _ = 0 := by rw [hz,mul_zero]

theorem weightedPairing_add {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (K L : ι → ι → ℝ) (A B : Poly2) :
    weightedPairing node (fun p q => K p q+L p q) A B =
      weightedPairing node K A B + weightedPairing node L A B := by
  simp [weightedPairing, add_mul, add_div, Finset.sum_add_distrib]

theorem evalTwo_difference_mul (u v : ℝ) (A B : Poly2) :
    evalTwo u v ((MvPolynomial.X 0-MvPolynomial.X 1)*A*B) =
      (u-v)*evalTwo u v A*evalTwo u v B := by
  simp [evalTwo]

theorem pairing_row_column_invariant {ι : Type*} [Fintype ι]
    (s : ℕ) (hs : 2 ≤ s) (hc : Fintype.card ι = 2*s)
    (node : ι → ℝ) (hn : Function.Injective node) (K : ι → ι → ℝ)
    (r c : ι → ℝ) (A B : Poly2)
    (hA : A ∈ rectangle (s-1) (s-2))
    (hB : B ∈ rectangle (s-2) (s-1)) :
    weightedPairing node (fun p q => K p q+r p+c q) A B =
      weightedPairing node K A B := by
  classical
  let C : Poly2 := (MvPolynomial.X 0-MvPolynomial.X 1)*A*B
  have hC (i : Fin 2) : C.degreeOf i + 1 < Fintype.card ι := by
    have hA := (rectangle_membership _ _ A).mp hA
    have hB := (rectangle_membership _ _ B).mp hB
    have h1 := MvPolynomial.degreeOf_mul_le i ((MvPolynomial.X 0-MvPolynomial.X 1)*A) B
    have h2 := MvPolynomial.degreeOf_mul_le i (MvPolynomial.X 0-MvPolynomial.X 1) A
    have h3 := MvPolynomial.degreeOf_sub_le i (MvPolynomial.X 0 : Poly2) (MvPolynomial.X 1)
    change C.degreeOf i ≤ _ at h1
    rw [hc]
    fin_cases i <;> norm_num [MvPolynomial.degreeOf_X, Fin.ext_iff] at h1 h2 h3 ⊢ <;> omega
  have hr : weightedPairing node (fun p _ => r p) A B = 0 := by
    unfold weightedPairing
    apply Finset.sum_eq_zero
    intro p _
    calc
      (∑q, r p*(node p-node q)/
        (Zarankiewicz.derivativeAtNode node p*Zarankiewicz.derivativeAtNode node q)*
        evalTwo (node p) (node q) A*evalTwo (node p) (node q) B) =
        (r p/Zarankiewicz.derivativeAtNode node p) *
        ∑q, evalTwo (node p) (node q) C/Zarankiewicz.derivativeAtNode node q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _
          rw [show evalTwo (node p) (node q) C = _ from evalTwo_difference_mul _ _ A B]
          ring
      _ = 0 := by rw [weighted_evalTwo_second_zero node hn _ C (hC 1), mul_zero]
  have hcol : weightedPairing node (fun _ q => c q) A B = 0 := by
    unfold weightedPairing
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q _
    calc
      (∑p, c q*(node p-node q)/
        (Zarankiewicz.derivativeAtNode node p*Zarankiewicz.derivativeAtNode node q)*
        evalTwo (node p) (node q) A*evalTwo (node p) (node q) B) =
        (c q/Zarankiewicz.derivativeAtNode node q) *
        ∑p, evalTwo (node p) (node q) C/Zarankiewicz.derivativeAtNode node p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          rw [show evalTwo (node p) (node q) C = _ from evalTwo_difference_mul _ _ A B]
          ring
      _ = 0 := by rw [weighted_evalTwo_first_zero node hn _ C (hC 0), mul_zero]
  rw [weightedPairing_add, weightedPairing_add, hr, hcol, add_zero, add_zero]

end Paper170

end
end

section

/-! Coefficient spaces for the even-node interpolation argument. -/
noncomputable section
open scoped BigOperators
open Module
namespace Paper170

def exponentPair : (Fin 2 →₀ ℕ) ≃ ℕ × ℕ where
  toFun m := (m 0, m 1)
  invFun p := Finsupp.equivFunOnFinite.symm ![p.1, p.2]
  left_inv m := by
    ext i
    fin_cases i <;> simp
  right_inv p := by simp

@[simp] theorem exponentPair_symm_zero (a b : ℕ) : exponentPair.symm (a,b) 0 = a := rfl
@[simp] theorem exponentPair_symm_one (a b : ℕ) : exponentPair.symm (a,b) 1 = b := rfl

theorem rectangle_eq_restrictSupport (a b : ℕ) :
    rectangle a b = MvPolynomial.restrictSupport ℝ {m | m 0 ≤ a ∧ m 1 ≤ b} := by
  ext P
  rw [rectangle_membership, MvPolynomial.mem_restrictSupport_iff]
  simp only [MvPolynomial.degreeOf_le_iff, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]
  exact ⟨fun h m hm => ⟨h.1 m hm, h.2 m hm⟩,
    fun h => ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩⟩

def rectangleExponentEquiv (a b : ℕ) :
    {m : Fin 2 →₀ ℕ // m 0 ≤ a ∧ m 1 ≤ b} ≃ Fin (a+1) × Fin (b+1) where
  toFun m := (⟨m.val 0, by omega⟩, ⟨m.val 1, by omega⟩)
  invFun p := ⟨exponentPair.symm (p.1.val,p.2.val), by simp; omega⟩
  left_inv m := by
    apply Subtype.ext
    exact exponentPair.symm_apply_apply m.val
  right_inv p := by rfl

def rectangleBasis (a b : ℕ) : Basis (Fin (a+1) × Fin (b+1)) ℝ (rectangle a b) :=
  ((MvPolynomial.basisRestrictSupport ℝ _).reindex (rectangleExponentEquiv a b)).map
    (LinearEquiv.ofEq _ _ (rectangle_eq_restrictSupport a b).symm)

theorem rectangle_finite (a b : ℕ) : FiniteDimensional ℝ (rectangle a b) :=
  Module.Finite.of_basis (rectangleBasis a b)

theorem rectangle_dimension (a b : ℕ) :
    Module.finrank ℝ (rectangle a b) = (a+1)*(b+1) := by
  rw [Module.finrank_eq_card_basis (rectangleBasis a b)]
  simp

/-- The coefficient-preserving bridge to the existing bivariate interpolation library. -/
def toBiPolynomial : Poly2 ≃ₗ[ℝ] Zarankiewicz.BiPoly :=
  ((MvPolynomial.basisMonomials (Fin 2) ℝ).repr.trans
    (Finsupp.domLCongr exponentPair)).trans Zarankiewicz.flattenBi.symm

theorem toBiPolynomial_coeff (P : Poly2) (a b : ℕ) :
    Zarankiewicz.biCoeff (toBiPolynomial P) a b =
      P.coeff (exponentPair.symm (a,b)) := by
  rw [← Zarankiewicz.flattenBi_apply]
  change (Zarankiewicz.flattenBi (Zarankiewicz.flattenBi.symm _)) _ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem toBiPolynomial_monomial (m : Fin 2 →₀ ℕ) (c : ℝ) :
    toBiPolynomial (MvPolynomial.monomial m c) =
      PolynomialModule.single ℝ (m 0) (PolynomialModule.single ℝ (m 1) c) := by
  apply Zarankiewicz.bi_ext
  intro a b
  rw [toBiPolynomial_coeff]
  simp only [MvPolynomial.coeff_monomial, Zarankiewicz.biCoeff,
    PolynomialModule.coeff_single, Finsupp.single_apply]
  by_cases hm : m = exponentPair.symm (a,b)
  · subst m
    simp
  · have hne : m 0 ≠ a ∨ m 1 ≠ b := by
      by_contra h
      simp only [not_or, not_not] at h
      apply hm
      apply exponentPair.injective
      exact Prod.ext h.1 h.2
    rcases hne with h | h
    · simp [hm, h]
    · by_cases ha : m 0 = a <;> simp [hm, h, ha]

theorem toBiPolynomial_eval (P : Poly2) (u v : ℝ) :
    Zarankiewicz.biEval u v (toBiPolynomial P) = evalTwo u v P := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial m c =>
    rw [toBiPolynomial_monomial]
    simp only [Zarankiewicz.biEval, LinearMap.comp_apply, PolynomialModule.eval_single,
      map_smul, smul_eq_mul]
    simp only [evalTwo, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_two]
      ring
    · intro i
      simp

theorem toBiPolynomial_bounded (a b : ℕ) (P : Poly2) (hP : P ∈ rectangle a b) :
    Zarankiewicz.BiBounded (a+1) (b+1) (toBiPolynomial P) := by
  obtain ⟨ha,hb⟩ := (rectangle_membership a b P).mp hP
  constructor
  · intro k hk
    apply PolynomialModule.ext
    apply Finsupp.ext
    intro j
    change Zarankiewicz.biCoeff (toBiPolynomial P) k j = 0
    rw [toBiPolynomial_coeff]
    by_contra h
    have := MvPolynomial.degreeOf_le_iff.mp ha _ (MvPolynomial.mem_support_iff.mpr h)
    simp only [exponentPair_symm_zero] at this
    omega
  · intro k j hj
    change Zarankiewicz.biCoeff (toBiPolynomial P) k j = 0
    rw [toBiPolynomial_coeff]
    by_contra h
    have := MvPolynomial.degreeOf_le_iff.mp hb _ (MvPolynomial.mem_support_iff.mpr h)
    simp only [exponentPair_symm_one] at this
    omega

end Paper170

end
end

section

/-! Polynomial cycle tests and the span of products of bounded-degree polynomials. -/
noncomputable section
open scoped BigOperators
namespace Paper170

def polynomialTestLinear {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) : Poly4 →ₗ[ℝ] ℝ :=
  ∑ i, ∑ p, ∑ k, ∑ q,
    (J i p k q * nodeWeight node i * nodeWeight node p * nodeWeight node k * nodeWeight node q) •
      evalFour (node i) (node p) (node k) (node q)

theorem polynomialTestLinear_apply {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) (P : Poly4) :
    polynomialTestLinear node J P = polynomialTest node J P := by
  simp [polynomialTestLinear, polynomialTest]

theorem evalFour_monomial (x u y v : ℝ) (m : Fin 4 →₀ ℕ) (c : ℝ) :
    evalFour x u y v (MvPolynomial.monomial m c) = c * (x^m 0 * u^m 1 * y^m 2 * v^m 3) := by
  simp only [evalFour, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
    Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_four]
  · intro i
    simp

theorem polynomialTest_monomial {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (m : Fin 4 →₀ ℕ) (c : ℝ) :
    polynomialTest node J (MvPolynomial.monomial m c) = c *
      chainPairing J (weightedChain node (m 0) (m 1)) (weightedChain node (m 2) (m 3)) := by
  simp only [polynomialTest, evalFour_monomial, chainPairing, Finset.mul_sum, weightedChain]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem polynomial_cycle_tests {n : ℕ} (hn : 2 ≤ n) (node : Fin n → ℝ)
    (hnode : Function.Injective node) (J : CrossingTensor n)
    (hcycles : ∀ z z' : Fin n → Fin n → ℝ,
      (∀ v, chainBoundary z v = 0) → (∀ v, chainBoundary z' v = 0) →
        chainPairing J z z' = 0)
    (H : Poly4) (hH : H ∈ box4 (n-2)) : polynomialTest node J H = 0 := by
  rw [← polynomialTestLinear_apply, H.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [polynomialTestLinear_apply, polynomialTest_monomial]
  have hb (i : Fin 4) : m i + 1 < n := by
    have := MvPolynomial.degreeOf_le_iff.mp ((box4_membership (n-2) H).mp hH i) m hm
    omega
  rw [hcycles _ _ (weighted_chain_boundary node hnode _ _ (hb 0) (hb 1))
    (weighted_chain_boundary node hnode _ _ (hb 2) (hb 3)), mul_zero]

theorem products_span_degree (s : ℕ) :
    Submodule.span ℝ {P : Polynomial ℝ | ∃ U V : Polynomial ℝ,
      U.natDegree ≤ s ∧ V.natDegree ≤ s ∧ P = U * V} = Polynomial.degreeLT ℝ (2*s+1) := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro P ⟨U,V,hU,hV,rfl⟩
    change U * V ∈ Polynomial.degreeLT ℝ (2*s+1)
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have := Polynomial.natDegree_mul_le_of_le hU hV
    omega
  · rw [Polynomial.degreeLT_eq_span_X_pow, Submodule.span_le]
    intro P hP
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hP
    have hk : k ≤ 2*s := by rw [Finset.mem_range] at hk; omega
    apply Submodule.subset_span
    refine ⟨Polynomial.X ^ min k s, Polynomial.X ^ (k-min k s), ?_, ?_, ?_⟩
    · simp only [Polynomial.natDegree_X_pow]
      exact min_le_right _ _
    · simp only [Polynomial.natDegree_X_pow]
      omega
    · rw [← pow_add, Nat.add_sub_of_le (min_le_left k s)]

end Paper170

end
end

end OAI
