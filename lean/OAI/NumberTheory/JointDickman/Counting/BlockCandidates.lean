import OAI.NumberTheory.JointDickman.Amplification.CandidateCountScale
import OAI.NumberTheory.JointDickman.Amplification.CandidateWeightCap

namespace OAI

/-! # The finite candidate representations determined by endpoint types -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def endpointSplits (B L : ℕ) (τ C : ℝ) (S : Finset ℕ) : Finset (Finset ℕ) :=
  S.powerset.filter (fun A => RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A))

theorem mem_endpointSplits {B L : ℕ} {τ C : ℝ} {S A : Finset ℕ} :
    A ∈ endpointSplits B L τ C S ↔
      A ⊆ S ∧ RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A) := by
  classical
  simp [endpointSplits]

theorem endpointSplits_card {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, ∀ S : Finset ℕ,
      (endpointSplits B L τ C S).card ≤ B := by
  classical
  filter_upwards [regular_endpoint_subset_count hL hτ hτsmall] with B hB
  intro C S
  by_cases hn : (endpointSplits B L τ C S).Nonempty
  · obtain ⟨A,hA⟩ := hn
    obtain ⟨hAS,hreg,hrem⟩ := mem_endpointSplits.mp hA
    have hcount := hB C A (S \ A) hreg hrem
    have he : A ∪ (S \ A) = S := union_sdiff_of_subset hAS
    rw [he] at hcount
    exact (card_le_card (filter_subset _ _)).trans (by simpa only [card_powerset] using hcount)
  · simp only [not_nonempty_iff_eq_empty.mp hn,card_empty]
    exact Nat.zero_le B

abbrev BlockCandidateIndex (M : ℕ) := (Fin M × Fin M) × (Finset ℕ × Finset ℕ)

/-- Lower and upper endpoint subsets; the coefficient c is determined by
these two subset products and the positive lag. -/
noncomputable def candidateLow {M : ℕ} (e : BlockCandidateIndex M) : ℕ := ∏ p ∈ e.2.1, p
noncomputable def candidateHigh {M : ℕ} (e : BlockCandidateIndex M) : ℕ := ∏ p ∈ e.2.2, p
def candidateLag {M : ℕ} (e : BlockCandidateIndex M) : ℕ := e.1.2.val-e.1.1.val
noncomputable def candidateQuotient {M : ℕ} (e : BlockCandidateIndex M) : ℕ :=
  (candidateHigh e-candidateLow e)/candidateLag e

open Classical in
noncomputable def blockCandidatePool (B L M : ℕ) (τ C : ℝ) (S : Fin M → Finset ℕ) :
    Finset (BlockCandidateIndex M) :=
  (univ : Finset (Fin M × Fin M)).biUnion (fun ik =>
    ((endpointSplits B L τ C (S ik.1)).product (endpointSplits B L τ C (S ik.2))).image
      (fun ab => (ik,ab)))

def BlockCandidateAdmissible {M : ℕ} (B L T H : ℕ) (τ C : ℝ)
    (e : BlockCandidateIndex M) : Prop :=
  e.1.1 < e.1.2 ∧ H < candidateLag e ∧ candidateLag e < T ∧
  0 < candidateQuotient e ∧
  candidateHigh e = candidateLow e+candidateLag e*candidateQuotient e ∧
  (candidateLow e).Coprime (candidateHigh e) ∧
  (candidateLow e).Coprime (candidateQuotient e) ∧
  (candidateHigh e).Coprime (candidateQuotient e) ∧
  candidateQuotient e = ∏ p ∈ coefficientPrimeSet B (candidateQuotient e), p ∧
  RegularPrimeSet B L τ C (coefficientPrimeSet B (candidateQuotient e)) ∧
  (B : ℝ) ≤ Real.log (candidateQuotient e) ∧
  Real.log (candidateQuotient e) ≤ 2*B ∧
  T*candidateQuotient e ≤ candidateLow e ∧ candidateLow e ≤ 2*T*candidateQuotient e ∧
  T*candidateQuotient e ≤ candidateHigh e ∧ candidateHigh e ≤ 2*T*candidateQuotient e

open Classical in
noncomputable def blockCandidates (B L T H M : ℕ) (τ C : ℝ) (S : Fin M → Finset ℕ) :
    Finset (BlockCandidateIndex M) :=
  (blockCandidatePool B L M τ C S).filter (BlockCandidateAdmissible B L T H τ C)

theorem blockCandidatePool_card {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (M : ℕ) (S : Fin M → Finset ℕ),
      (blockCandidatePool B L M τ C S).card ≤ M^2*B^2 := by
  classical
  filter_upwards [endpointSplits_card hL hτ hτsmall] with B hB
  intro C M S
  unfold blockCandidatePool
  calc
    _ ≤ ∑ ik : Fin M × Fin M,
        (((endpointSplits B L τ C (S ik.1)).product
          (endpointSplits B L τ C (S ik.2))).image (fun ab => (ik,ab))).card := card_biUnion_le
    _ ≤ ∑ _ik : Fin M × Fin M, B*B := by
      apply sum_le_sum
      intro ik _
      exact card_image_le.trans (by
        rw [Finset.product_eq_sprod,Finset.card_product]
        exact Nat.mul_le_mul (hB C (S ik.1)) (hB C (S ik.2)))
    _ = _ := by simp [pow_two,mul_assoc]

theorem blockCandidates_card {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ) (S : Fin M → Finset ℕ),
      (blockCandidates B L T H M τ C S).card ≤ M^2*B^2 := by
  classical
  filter_upwards [blockCandidatePool_card hL hτ hτsmall] with B hB
  intro C T H M S
  exact (card_le_card (filter_subset _ _)).trans (hB C M S)

end JointDickman

end OAI
