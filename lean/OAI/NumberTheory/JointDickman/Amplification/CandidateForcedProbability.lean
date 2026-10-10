import OAI.NumberTheory.JointDickman.Amplification.CandidateForcedConditional
import OAI.NumberTheory.JointDickman.Probability.SitePartitionProbability

namespace OAI

/-! # Forced occupied-prime hits in the actual random candidate list -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

def ForcedCandidateHit (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ e ∈ blockCandidates B L T H M τ C S, CandidateForcedWitness B e S

open Classical in
theorem forcedCandidateHit_pair_event {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} (h : ForcedCandidateHit B L T H M τ C S) :
    ∃ ik : Fin M × Fin M, PairForcedEvent B L T H M τ C ik.1 ik.2 S := by
  obtain ⟨e,he,hw⟩ := h
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  refine ⟨e.1,e.2,?_,ha,hw⟩
  simpa only [pairSplitChoices,Finset.product_eq_sprod,mem_product] using hs

open Classical in
theorem pairForcedEvent_probability {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), (T : ℝ) ≤ Real.exp B → (M : ℝ) ≤ Real.exp B → ∀ (i k : Fin M),
      finiteProbability (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => PairForcedEvent B L T H M τ C i k (fun s => (S s).val)) ≤
        (B : ℝ)^2*(M : ℝ)*(5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) := by
  filter_upwards [pairForcedEvent_conditional_bound hL hτ hτsmall] with B hB
  intro C T H M hT hM i k
  apply siteProduct_probability_of_conditional_bound _
    (fun _ => independentPrimeSetMass_nonneg B)
    (fun _ => independentPrimeSetMass_sum B) {i,k}
  exact hB C T H M hT hM i k

open Classical in
/-- Exposing endpoints first makes the union bound valid for the actual
candidate family, although that family depends on the random sites. -/
theorem forcedCandidateHit_probability {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), (T : ℝ) ≤ Real.exp B → (M : ℝ) ≤ Real.exp B →
      finiteProbability (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => ForcedCandidateHit B L T H M τ C (fun s => (S s).val)) ≤
        5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B) := by
  filter_upwards [pairForcedEvent_probability hL hτ hτsmall] with B hB
  intro C T H M hT hM
  let w := siteProductMass (fun _ : Fin M => independentPrimeSetMass B)
  have hw : ∀ S, 0 ≤ w S := siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)
  calc
    _ ≤ finiteProbability w (fun S => ∃ ik : Fin M × Fin M,
        PairForcedEvent B L T H M τ C ik.1 ik.2 (fun s => (S s).val)) := by
      apply finiteProbability_mono w hw
      intro S hS
      exact forcedCandidateHit_pair_event hS
    _ ≤ ∑ ik : Fin M × Fin M, finiteProbability w
        (fun S => PairForcedEvent B L T H M τ C ik.1 ik.2 (fun s => (S s).val)) :=
      finiteProbability_union_le w hw _
    _ ≤ ∑ _ik : Fin M × Fin M, (B : ℝ)^2*(M : ℝ)*(5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) :=
      sum_le_sum (fun ik _ => hB C T H M hT hM ik.1 ik.2)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]; ring

end JointDickman

end OAI
