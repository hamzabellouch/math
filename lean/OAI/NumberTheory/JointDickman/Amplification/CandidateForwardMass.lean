import OAI.NumberTheory.JointDickman.Amplification.CandidateConditionalMean
import OAI.NumberTheory.JointDickman.Probability.CandidateKernelMass
import OAI.NumberTheory.JointDickman.Counting.ForwardLagSum

namespace OAI

/-! # Forward candidate mass and the vanishing independent-root error -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

/-- Each candidate is counted once in the strict upper triangle. -/
theorem candidateMatrix_forward_total {ι : Type*} [Fintype ι] {M : ℕ}
    (row col : ι → Fin M) (v : ι → ℝ) (hord : ∀ e, row e < col e) :
    (∑ i : Fin M, ∑ k : Fin M, if i < k then candidateMatrix row col v i k else 0) = ∑ e, v e := by
  classical
  have hpoint (i k : Fin M) (e : ι) :
      (if i < k then
        (if i = row e then if k = col e then v e else 0 else 0)+
        (if i = col e then if k = row e then v e else 0 else 0)
        else 0) = (if i = row e then if k = col e then v e else 0 else 0) := by
    by_cases hik : i < k
    · rw [ite_eq_left hik]
      have hz : (if i = col e then if k = row e then v e else 0 else 0) = 0 := by
        split_ifs with hi hk
        · have ho : k < i := by simpa only [hi,hk] using hord e
          exact False.elim ((not_lt_of_ge hik.le) ho)
        · rfl
        · rfl
      rw [hz,add_zero]
    · rw [ite_eq_right hik]
      symm
      split_ifs with hi hk
      · have ho : i < k := by simpa only [hi,hk] using hord e
        exact False.elim (hik ho)
      · rfl
      · rfl

  have hexpand (i k : Fin M) :
      (if i < k then candidateMatrix row col v i k else 0) =
        ∑ e, if i < k then
          (if i = row e then if k = col e then v e else 0 else 0)+
          (if i = col e then if k = row e then v e else 0 else 0) else 0 := by
    by_cases h : i < k
    · simp only [h,ite_true,candidateMatrix]
    · simp only [h,ite_false,sum_const_zero]
  simp_rw [hexpand,hpoint]
  calc
    _ = ∑ e : ι, ∑ i : Fin M, ∑ k : Fin M,
        (if i = row e then if k = col e then v e else 0 else 0) := by
      conv_lhs => arg 2; ext i; rw [sum_comm]
      rw [sum_comm]
    _ = _ := by simp

/-- The forward entry is zero once its lag is outside the candidate support. -/
theorem latentCandidateKernel_forward_zero {B L T H M : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i k : Fin M)
    (hik : i < k) (hlag : T ≤ k.val-i.val) :
    latentCandidateKernel B L T H M τ C S χ i k = 0 := by
  classical
  rw [latentCandidateKernel_pair B L T H τ C S χ i k hik]
  apply sum_eq_zero
  intro A _
  apply sum_eq_zero
  intro D _
  have hn : ¬ BlockCandidateAdmissible B L T H τ C ((i,k),(A,D)) := by
    intro he
    have ht := he.2.2.1
    change k.val-i.val < T at ht
    omega
  exact ite_eq_right hn

/-- The conditional forward bounds have an absolute total per block row. -/
theorem latentCandidateKernel_forward_total_mean
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, χ e ≤ 1) →
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => ∑ i : Fin M, ∑ k : Fin M,
          if i < k then latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k else 0) ≤
        K*M := by
  classical
  obtain ⟨K,hK,hbound⟩ := latentCandidateKernel_forward_mean hFord hM
  refine ⟨K*Real.exp 24,by positivity,?_⟩
  filter_upwards [hbound] with B hbound
  intro L T H M τ C hT hTs χ hχ
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  simp_rw [finiteExpectation_sum]
  calc
    _ ≤ ∑ i : Fin M, ∑ k : Fin M,
        if i < k ∧ k.val-i.val < T then K/(T : ℝ)*singularFactor 24 (k.val-i.val) else 0 := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro k _
      by_cases hik : i < k
      · simp only [hik,ite_true,true_and]
        by_cases ht : k.val-i.val < T
        · simp only [ht,ite_true]
          exact hbound L T H M τ C hT hTs χ hχ i k hik
        · simp only [ht,ite_false]
          have hz (S : Fin M → (auxiliaryPrimes B).powerset) :=
            latentCandidateKernel_forward_zero (B := B) (L := L) (T := T) (H := H) (τ := τ) (C := C)
              (fun i => (S i).val) χ i k hik (by omega)
          simp only [hz,finiteExpectation,mul_zero,sum_const_zero,le_refl]
      · simp only [hik,ite_false,false_and,finiteExpectation,mul_zero,sum_const_zero,le_refl]
    _ = ∑ i : Fin M, K/(T : ℝ)*
        ∑ k : Fin M, if i < k ∧ k.val-i.val < T then singularFactor 24 (k.val-i.val) else 0 := by
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      split_ifs <;> simp only [mul_zero]
    _ ≤ ∑ _i : Fin M, K/(T : ℝ)*(Real.exp 24*T) :=
      sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (forward_lag_singular_sum i T)
        (div_nonneg hK.le hTr.le))
    _ = _ := by simp; field_simp

end JointDickman

end OAI
