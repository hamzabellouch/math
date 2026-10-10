import OAI.InformationTheory.QuantumCircuit.Reflection
import OAI.InformationTheory.QuantumCircuit.Polynomial

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma conjugate_finset_sum {A ι : Type*} [CStarAlgebra A] (U : A) (s : Finset ι) (f : ι → A) :
    conjugate U (∑ i ∈ s, f i) = ∑ i ∈ s, conjugate U (f i) := by
  simp only [conjugate,Finset.mul_sum,Finset.sum_mul]

lemma Count.polynomial_norm_le {N : ℕ} (D : Count N) (p : Polynomial ℝ) :
    ‖D.polynomial p‖ ≤ weight N p := by
  classical
  rw [D.polynomial_eq_sum]
  apply (norm_sum_le _ _).trans
  change (∑ k ∈ p.support, ‖p.coeff k • D.operator^k‖) ≤ ∑ k ∈ p.support, |p.coeff k| *(N:ℝ)^k
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) D.operator_norm_le _)

lemma Count.monomial_transition {N : ℕ} (D M : Count N) (U : Operator N) (r μ δ : ℝ)
    (hδ : 0 ≤ δ) (k : ℕ) (hk : (k:ℝ) ≤ μ)
    (hA : ∀ A : Count N, (A.support.card:ℝ) ≤ μ →
      ‖M.high r*conjugate U A.zero*M.zero‖ ≤ δ) :
    ‖M.high r*conjugate U (D.operator^k)*M.zero‖ ≤ (N:ℝ)^k*δ := by
  rw [D.operator_monomials,conjugate_list_sum,← List.sum_map_mul_left,← List.sum_map_mul_right]
  have h := list_norm_sum_le_const (selectionSets D.support k)
    (fun F => M.high r*conjugate U ((D.flip D.support).restrict F).zero*M.zero) δ (by
      intro F hF
      apply hA
      have hc := ((D.flip D.support).restrict_support_card F).trans (selectionSets_card _ _ F hF)
      exact (show (((D.flip D.support).restrict F).support.card:ℝ) ≤ k by exact_mod_cast hc).trans hk)
  apply h.trans
  rw [selectionSets_length]
  apply mul_le_mul_of_nonneg_right _ hδ
  exact_mod_cast Nat.pow_le_pow_left (show D.support.card ≤ N by simpa using Finset.card_le_univ D.support) k

lemma Count.polynomial_transition {N : ℕ} (D M : Count N) (U : Operator N)
    (p : Polynomial ℝ) (r μ δ : ℝ) (hδ : 0 ≤ δ) (hp : (p.natDegree:ℝ) ≤ μ)
    (hA : ∀ A : Count N, (A.support.card:ℝ) ≤ μ →
      ‖M.high r*conjugate U A.zero*M.zero‖ ≤ δ) :
    ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ weight N p*δ := by
  classical
  rw [D.polynomial_eq_sum,conjugate_finset_sum,Finset.mul_sum,Finset.sum_mul]
  simp only [conjugate_smul,mul_smul_comm,smul_mul_assoc]
  apply (norm_sum_le _ _).trans
  change (∑ k ∈ p.support, ‖p.coeff k • (M.high r*conjugate U (D.operator^k)*M.zero)‖) ≤
    (∑ k ∈ p.support, |p.coeff k| *(N:ℝ)^k)*δ
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_smul,Real.norm_eq_abs]
  rw [mul_assoc (|p.coeff k|) ((N:ℝ)^k)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply D.monomial_transition M U r μ δ hδ k _ hA
  exact (show (k:ℝ) ≤ p.natDegree by exact_mod_cast Polynomial.le_natDegree_of_mem_supp k hk).trans hp

lemma Count.backward_finite {N : ℕ} (M D : Count N) (U : Operator N) (hU : U ∈ unitary (Operator N))
    (p : Polynomial ℝ) (r b A B E T : ℝ)
    (hx : ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ A)
    (hp : ‖D.polynomial p‖ ≤ B)
    (he : ‖(D.zero-D.polynomial p)*D.low b‖ ≤ E)
    (ht : ‖D.high b*star U*M.zero*U*D.zero‖ ≤ T) :
    ‖M.high r*conjugate U D.zero*M.zero‖^2 ≤ A+E+(1+B)*T := by
  let Q := conjugate U D.zero
  let X := conjugate U (D.polynomial p)
  let W := conjugate U (D.high b)
  have hQ : IsStarProjection Q := conjugate_projection hU D.zero_projection
  have hQn : ‖Q‖ ≤ 1 := IsStarProjection.norm_le _ hQ
  have hXn : ‖X‖ ≤ B := by
    change ‖U*D.polynomial p*star U‖ ≤ B
    rw [norm_unitary_conjugate hU]
    exact hp
  have hn : ‖Q-X‖ ≤ 1+B := (norm_sub_le _ _).trans (add_le_add hQn hXn)
  have hlow : ‖(Q-X)*(1-W)‖ ≤ E := by
    have heq : (Q-X)*(1-W) = conjugate U ((D.zero-D.polynomial p)*D.low b) := by
      change (conjugate U D.zero-conjugate U (D.polynomial p))*(1-conjugate U (D.high b)) = _
      simp only [Count.low,conjugate_mul hU,conjugate_sub,conjugate_one hU]
    rw [heq]
    change ‖U*((D.zero-D.polynomial p)*D.low b)*star U‖ ≤ E
    rw [norm_unitary_conjugate hU]
    exact he
  have htail : ‖W*M.zero*Q‖ ≤ T := by
    have heq : W*M.zero*Q = conjugate U (D.high b*star U*M.zero*U*D.zero) := by
      dsimp only [W,Q,conjugate]
      simp only [mul_assoc]
    rw [heq]
    change ‖U*(D.high b*star U*M.zero*U*D.zero)*star U‖ ≤ T
    rw [norm_unitary_conjugate hU]
    exact ht
  have herr : ‖(Q-X)*M.zero*Q‖ ≤ E+(1+B)*T := by
    apply (norm_split_bound (Q-X) W M.zero Q (IsStarProjection.norm_le _ M.zero_projection) hQn).trans
    exact add_le_add hlow (mul_le_mul hn htail (norm_nonneg _) ((norm_nonneg _).trans hn))
  have hsquare := projection_transition_square (M.high r) M.zero Q X
    (M.high_projection r) M.zero_projection hQ
  exact hsquare.trans ((add_le_add hx herr).trans_eq (by ring))

end QAC

end

end OAI
