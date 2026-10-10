import OAI.NumberTheory.JointDickman.Counting.BlockCandidates
import OAI.NumberTheory.JointDickman.Amplification.RootCutDecay

namespace OAI

/-! # Independent auxiliary-root weights for the actual candidate list -/

namespace JointDickman
open Finset Filter
open PublishedInputs
open scoped Topology

/-- The five endpoint/coefficient factors and the sixth, auxiliary-root
factor in the manuscript's kernel, including its normalization. -/
noncomputable def candidateRootWeight {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (e : BlockCandidateIndex M) (R : Finset ℕ) : ℝ :=
  (regularCoefficientWeight B L τ C (candidateLow e) *
    regularResidueWeight B L τ C (S e.1.1 \ e.2.1) *
    (regularCoefficientWeight B L τ C (candidateHigh e) *
      regularResidueWeight B L τ C (S e.1.2 \ e.2.2)) *
    (regularCoefficientWeight B L τ C (candidateQuotient e) *
      regularResidueWeight B L τ C R))/(B : ℝ) * χ e

noncomputable def independentPrimeSetMass (B : ℕ) (R : (auxiliaryPrimes B).powerset) : ℝ :=
  bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R.val

theorem independentPrimeSetMass_nonneg (B : ℕ) (R : (auxiliaryPrimes B).powerset) :
    0 ≤ independentPrimeSetMass B R := by
  apply bernoulliSubsetMass_nonneg (mem_powerset.mp R.property)
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).one_le
  exact ⟨by positivity, (div_le_one (by linarith : (0 : ℝ) < p)).mpr hp1⟩

theorem independentPrimeSetMass_sum (B : ℕ) : (∑ R, independentPrimeSetMass B R) = 1 := by
  exact (sum_coe_sort _ _).trans (bernoulliSubsetMass_sum _ _)

theorem candidateRootWeight_nonneg {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hχ : ∀ e, 0 ≤ χ e) (e : BlockCandidateIndex M) (R : Finset ℕ) :
    0 ≤ candidateRootWeight B L τ C S χ e R := by
  unfold candidateRootWeight
  exact mul_nonneg (div_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
        (regularResidueWeight_nonneg _ _ _ _ _))
        (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
          (regularResidueWeight_nonneg _ _ _ _ _)))
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
        (regularResidueWeight_nonneg _ _ _ _ _))) (Nat.cast_nonneg B)) (hχ e)

theorem candidateRootWeight_small {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (M : ℕ) (S : Fin M → Finset ℕ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, χ e ≤ 1) →
      ∀ (e : BlockCandidateIndex M) (R : Finset ℕ),
        candidateRootWeight B L τ C S χ e R ≤ (B : ℝ)^(-(7/100 : ℝ)) := by
  filter_upwards [six_regular_weights_small hL hτ hτsmall] with B hB
  intro C M S χ hχ e R
  have hn := candidateRootWeight_nonneg B L τ C S (fun _ => 1) (by simp) e R
  have he : candidateRootWeight B L τ C S χ e R =
      candidateRootWeight B L τ C S (fun _ => 1) e R * χ e := by
    simp only [candidateRootWeight,mul_one]
  rw [he]
  exact (mul_le_of_le_one_right hn (hχ e)).trans
    (by simpa only [candidateRootWeight,mul_one] using
      hB C (candidateLow e) (candidateHigh e) (candidateQuotient e)
          (S e.1.1 \ e.2.1) (S e.1.2 \ e.2.2) R)

noncomputable def candidateMeanWeight {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  finiteExpectation (independentPrimeSetMass B)
    (fun R => candidateRootWeight B L τ C S χ e R.val)

noncomputable def latentCandidateKernel (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) : Fin M → Fin M → ℝ :=
  candidateMatrix (fun e : blockCandidates B L T H M τ C S => e.val.1.1)
    (fun e => e.val.1.2) (fun e => candidateMeanWeight B L τ C S χ e.val)

noncomputable def independentCandidateKernel (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (R : blockCandidates B L T H M τ C S → (auxiliaryPrimes B).powerset) :
    Fin M → Fin M → ℝ :=
  candidateMatrix (fun e : blockCandidates B L T H M τ C S => e.val.1.1)
    (fun e => e.val.1.2) (fun e => candidateRootWeight B L τ C S χ e.val (R e).val)

theorem candidateMatrix_sub {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (row col : ι → κ) (v w : ι → ℝ) (i k : κ) :
    candidateMatrix row col (fun e => v e-w e) i k =
      candidateMatrix row col v i k-candidateMatrix row col w i k := by
  unfold candidateMatrix
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  split_ifs <;> ring

theorem candidate_root_fluctuation_bound {B L M : ℕ} (τ C : ℝ)
    (I : Finset (BlockCandidateIndex M)) (S : Fin M → Finset ℕ)
    (χ : BlockCandidateIndex M → ℝ) (hM : 0 < M) {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1/2)
    (hY : ∀ (e : I) (R : (auxiliaryPrimes B).powerset),
      0 ≤ candidateRootWeight B L τ C S χ e.val R.val ∧
        candidateRootWeight B L τ C S χ e.val R.val ≤ δ^2) :
    finiteExpectation (siteProductMass (fun _ : I => independentPrimeSetMass B))
      (fun R => kernelCutNorm (candidateMatrix (fun e : I => e.val.1.1)
        (fun e : I => e.val.1.2) (fun e : I =>
          candidateRootWeight B L τ C S χ e.val (R e).val-candidateMeanWeight B L τ C S χ e.val))) ≤
      δ*(3*Real.log 2+4*(∑ e : I, candidateMeanWeight B L τ C S χ e.val)/(M : ℝ)) := by
  have : NeZero M := ⟨hM.ne'⟩
  simpa only [candidateMeanWeight,Fintype.card_fin] using
    independent_candidate_cutNorm_small (ι := I)
    (Ω := (auxiliaryPrimes B).powerset) (κ := Fin M)
    (fun e : I => e.val.1.1) (fun e : I => e.val.1.2)
    (fun _ : I => independentPrimeSetMass B)
    (fun (e : I) (R : (auxiliaryPrimes B).powerset) =>
      candidateRootWeight B L τ C S χ e.val R.val)
    (fun _ R => independentPrimeSetMass_nonneg B R)
    (fun _ => independentPrimeSetMass_sum B) hδ hδsmall hY

theorem candidate_root_weight_square_cap {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop,
      0 < (B : ℝ)^(-(7/200 : ℝ)) ∧ (B : ℝ)^(-(7/200 : ℝ)) ≤ 1/2 ∧
      ∀ (C : ℝ) (M : ℕ) (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ),
      (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) → ∀ (e : BlockCandidateIndex M) (R : Finset ℕ),
        0 ≤ candidateRootWeight B L τ C S χ e R ∧
        candidateRootWeight B L τ C S χ e R ≤ ((B : ℝ)^(-(7/200 : ℝ)))^2 := by
  have hlim := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7/200)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [candidateRootWeight_small hL hτ hτsmall,
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2)),
    eventually_gt_atTop 0] with B hB hδsmall hB0
  refine ⟨Real.rpow_pos_of_pos (by exact_mod_cast hB0) _,hδsmall,?_⟩
  intro C M S χ hχ e R
  refine ⟨candidateRootWeight_nonneg B L τ C S χ (fun e => (hχ e).1) e R,?_⟩
  have hsq : ((B : ℝ)^(-(7/200 : ℝ)))^2 = (B : ℝ)^(-(7/100 : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg B)]
    congr 1
    norm_num
  rw [hsq]
  exact hB C M S χ (fun e => (hχ e).2) e R

/-- The estimate holds for the actual endpoint-dependent candidate list. -/
theorem actual_candidate_root_fluctuation {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), 0 < M →
      ∀ (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ),
      (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      finiteExpectation (siteProductMass (fun _ : blockCandidates B L T H M τ C S =>
        independentPrimeSetMass B)) (fun R => kernelCutNorm (fun i k =>
          independentCandidateKernel B L T H M τ C S χ R i k-
            latentCandidateKernel B L T H M τ C S χ i k)) ≤
        (B : ℝ)^(-(7/200 : ℝ))*(3*Real.log 2+
          4*(∑ e : blockCandidates B L T H M τ C S,
            candidateMeanWeight B L τ C S χ e.val)/(M : ℝ)) := by
  filter_upwards [candidate_root_weight_square_cap hL hτ hτsmall] with B hB
  intro C T H M hM S χ hχ
  have hh := candidate_root_fluctuation_bound τ C (blockCandidates B L T H M τ C S)
    S χ hM hB.1 hB.2.1 (fun e R => hB.2.2 C M S χ hχ e.val R.val)
  have heq (R : blockCandidates B L T H M τ C S → (auxiliaryPrimes B).powerset) :
      (fun i k => independentCandidateKernel B L T H M τ C S χ R i k-
        latentCandidateKernel B L T H M τ C S χ i k) =
      candidateMatrix (fun e : blockCandidates B L T H M τ C S => e.val.1.1)
        (fun e => e.val.1.2) (fun e => candidateRootWeight B L τ C S χ e.val (R e).val-
          candidateMeanWeight B L τ C S χ e.val) := by
    funext i k
    exact (candidateMatrix_sub _ _ _ _ i k).symm
  simp_rw [heq]
  exact hh

end JointDickman

end OAI
