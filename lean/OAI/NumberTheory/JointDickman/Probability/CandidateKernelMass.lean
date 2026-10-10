import OAI.NumberTheory.JointDickman.Probability.CandidateRootKernel

namespace OAI

/-! # Deterministic polynomial bounds for both candidate kernels -/

namespace JointDickman
open Finset Filter
open PublishedInputs
open scoped Topology

theorem candidateMatrix_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (hv : ∀ e, 0 ≤ v e) (i k : κ) :
    0 ≤ candidateMatrix row col v i k := by
  apply sum_nonneg
  intro e _
  apply add_nonneg <;> split_ifs <;> first | exact hv e | exact le_rfl

theorem candidateMatrix_total {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) :
    (∑ i, ∑ k, candidateMatrix row col v i k) = 2*∑ e, v e := by
  have h := candidateMatrix_bilinear row col v (fun _ => 1) (fun _ => 1)
  simp only [realBilinear,mul_one,one_add_one_eq_two] at h
  rw [← sum_mul] at h
  exact h.trans (mul_comm _ _)

theorem candidateMatrix_absolute_mass_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (hv : ∀ e, 0 ≤ v e ∧ v e ≤ 1) :
    (∑ i, ∑ k, |candidateMatrix row col v i k|) ≤ 2*(Fintype.card ι : ℝ) := by
  simp_rw [abs_of_nonneg (candidateMatrix_nonneg row col v (fun e => (hv e).1) _ _)]
  rw [candidateMatrix_total]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (sum_le_sum (fun e _ => (hv e).2)).trans_eq (by simp)

theorem candidateMeanWeight_nonneg {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hχ : ∀ e, 0 ≤ χ e) (e : BlockCandidateIndex M) :
    0 ≤ candidateMeanWeight B L τ C S χ e := by
  exact finiteExpectation_nonneg _ _ (independentPrimeSetMass_nonneg B)
    (fun R => candidateRootWeight_nonneg B L τ C S χ hχ e R.val)

theorem candidateWeight_and_mean_le_one {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (M : ℕ) (S : Fin M → Finset ℕ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      (∀ e R, candidateRootWeight B L τ C S χ e R ≤ 1) ∧
      (∀ e, candidateMeanWeight B L τ C S χ e ≤ 1) := by
  filter_upwards [candidateRootWeight_small hL hτ hτsmall,eventually_ge_atTop 1] with B hB hB1
  intro C M S χ hχ
  have hw (e : BlockCandidateIndex M) (R : Finset ℕ) :
      candidateRootWeight B L τ C S χ e R ≤ 1 :=
    (hB C M S χ (fun e => (hχ e).2) e R).trans
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hB1) (by norm_num))
  refine ⟨hw,?_⟩
  intro e
  exact (finiteExpectation_mono _ (independentPrimeSetMass_nonneg B)
    (fun R => hw e R.val)).trans_eq (by
      simp only [finiteExpectation,mul_one,independentPrimeSetMass_sum])

theorem candidate_kernels_polynomial_mass {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ) (S : Fin M → Finset ℕ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      (∑ i, ∑ k, |latentCandidateKernel B L T H M τ C S χ i k|) ≤
        2*(M : ℝ)^2*(B : ℝ)^2 ∧
      ∀ R, (∑ i, ∑ k, |independentCandidateKernel B L T H M τ C S χ R i k|) ≤
        2*(M : ℝ)^2*(B : ℝ)^2 := by
  filter_upwards [blockCandidates_card hL hτ hτsmall,
    candidateWeight_and_mean_le_one hL hτ hτsmall] with B hcard hweight
  intro C T H M S χ hχ
  have hcount : (Fintype.card (blockCandidates B L T H M τ C S) : ℝ) ≤ (M : ℝ)^2*(B : ℝ)^2 := by
    simpa only [Fintype.card_coe,Nat.cast_mul,Nat.cast_pow] using
      (show ((blockCandidates B L T H M τ C S).card : ℝ) ≤ (M^2*B^2 : ℕ) by
        exact_mod_cast hcard C T H M S)
  have hb := hweight C M S χ hχ
  constructor
  · exact (candidateMatrix_absolute_mass_le
      (fun e : blockCandidates B L T H M τ C S => e.val.1.1)
      (fun e : blockCandidates B L T H M τ C S => e.val.1.2)
      (fun e : blockCandidates B L T H M τ C S => candidateMeanWeight B L τ C S χ e.val)
      (fun e =>
      ⟨candidateMeanWeight_nonneg B L τ C S χ (fun e => (hχ e).1) e.val,hb.2 e.val⟩)).trans
      (by nlinarith only [hcount])
  · intro R
    exact (candidateMatrix_absolute_mass_le
      (fun e : blockCandidates B L T H M τ C S => e.val.1.1)
      (fun e : blockCandidates B L T H M τ C S => e.val.1.2)
      (fun e : blockCandidates B L T H M τ C S => candidateRootWeight B L τ C S χ e.val (R e).val)
      (fun e =>
      ⟨candidateRootWeight_nonneg B L τ C S χ (fun e => (hχ e).1) e.val (R e).val,
        hb.1 e.val (R e).val⟩)).trans (by nlinarith only [hcount])

end JointDickman

end OAI
