import OAI.NumberTheory.JointDickman.Amplification.RootComparisonScale
import OAI.NumberTheory.JointDickman.Amplification.CandidateRepeatProbability

namespace OAI

/-! # The product estimate for the actual endpoint-dependent candidate list -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem block_prime_twice_sites {B M p : ℕ} (hB : 2 ≤ B) (hM : M ≤ B^2)
    (hp : p ∈ auxiliaryPrimes B) : M < p ∧ 2*M ≤ p := by
  have hcut : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp hp).2
  have hpow : 2*M ≤ auxiliaryCutoff B := by
    change 2*M ≤ B^1000
    have hmul : B*B^2 = B^3 := by rw [pow_succ]; exact Nat.mul_comm _ _
    have hpower : B^3 ≤ B^1000 :=
      pow_le_pow_right₀ (show 1 ≤ B from Nat.le_trans (by decide : 1 ≤ 2) hB)
        (show (3 : ℕ) ≤ 1000 by decide)
    exact (Nat.mul_le_mul_left 2 hM).trans
      ((Nat.mul_le_mul_right (B^2) hB).trans (hmul.le.trans hpower))
  exact ⟨by omega,(hpow.trans hcut.le)⟩

theorem actual_candidate_roots_inj {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} (h : ¬ RepeatedCandidateRoot B L T H M τ C S) :
    Set.InjOn blockCandidateRoot (blockCandidates B L T H M τ C S : Set (BlockCandidateIndex M)) := by
  intro e he f hf hr
  by_contra hne
  exact h ⟨e,he,f,hf,hne,hr⟩

open Classical in
theorem actual_outside_candidate_product {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ) (S : Fin M → Finset ℕ),
      (T : ℝ) ≤ Real.exp B → (M : ℝ) ≤ Real.exp B → M ≤ B^2 →
      ¬ RepeatedCandidateRoot B L T H M τ C S →
      ∀ (Q : Finset ℕ) (hQ : Q ⊆ auxiliaryPrimes B),
      (∑ R, |outsideCandidateProductMass B (blockCandidates B L T H M τ C S) Q hQ R-
        bernoulliProductMass (blockCandidates B L T H M τ C S)
          (fun p : Q => fun _ => 1/(p.val : ℝ)) R|) ≤
        212*(B : ℝ)^19/(auxiliaryCutoff B : ℝ) := by
  filter_upwards [blockCandidates_card hL hτ hτsmall,eventually_ge_atTop 2] with B hcard hB
  intro C T H M S hT hMexp hM hroot Q hQ
  let I := blockCandidates B L T H M τ C S
  have hP : 0 < auxiliaryCutoff B := pow_pos (by omega) 1000
  have hs : (∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2) ≤ 1/(auxiliaryCutoff B : ℝ) :=
    sum_reciprocal_square_tail _ hP.ne' (fun p hp => by exact_mod_cast (mem_filter.mp hp).2)
  have hd := candidateDefectPrimes_mass hB hT hMexp hP I
    (fun _ he => (mem_blockCandidates.mp he).2) (actual_candidate_roots_inj hroot)
  exact (outsideCandidateProduct_l1 I Q hQ
    (fun p hp => (block_prime_twice_sites hB hM (hQ hp)).1)
    (fun p hp => (block_prime_twice_sites hB hM (hQ hp)).2)).trans
    (root_product_error_polynomial (by omega) hM (hcard C T H M S) hs hd)

end JointDickman

end OAI
