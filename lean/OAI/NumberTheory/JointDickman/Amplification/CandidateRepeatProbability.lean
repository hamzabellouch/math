import OAI.NumberTheory.JointDickman.Amplification.CandidateRepeatConditional
import OAI.NumberTheory.JointDickman.Probability.SitePartitionProbability

namespace OAI

/-! # Repeated rational roots in the actual random candidate list -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

def RepeatedCandidateRoot (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ e ∈ blockCandidates B L T H M τ C S,
    ∃ f ∈ blockCandidates B L T H M τ C S,
      e ≠ f ∧ blockCandidateRoot e = blockCandidateRoot f

open Classical in
theorem repeatedCandidateRoot_pair_event {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} (hS : ∀ i, S i ⊆ auxiliaryPrimes B)
    (h : RepeatedCandidateRoot B L T H M τ C S) :
    ∃ ik : Fin M × Fin M, PairRepeatEvent B L T H M τ C ik.1 ik.2 S := by
  obtain ⟨e,he,f,hf,hne,hr⟩ := h
  have hp : e.1 ≠ f.1 := fun hp => hne (blockCandidate_same_pair_root_unique hS he hf hp hr)
  exact ⟨e.1,coincident_candidates_pair_event he hf hp hr⟩

open Classical in
theorem pairRepeatEvent_probability {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), 0 < T → ∀ (i k : Fin M),
      finiteProbability (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => PairRepeatEvent B L T H M τ C i k (fun s => (S s).val)) ≤
        (B : ℝ)^2*(M : ℝ)/((T : ℝ)*Real.exp B) := by
  filter_upwards [pairRepeatEvent_conditional_bound hL hτ hτsmall] with B hB
  intro C T H M hT i k
  apply siteProduct_probability_of_conditional_bound _
    (fun _ => independentPrimeSetMass_nonneg B)
    (fun _ => independentPrimeSetMass_sum B) {i,k}
  exact hB C T H M hT i k

open Classical in
/-- Exposing endpoints first makes the union bound valid for the actual
candidate family, although that family depends on the random sites. -/
theorem repeatedCandidateRoot_probability {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), 0 < T →
      finiteProbability (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => RepeatedCandidateRoot B L T H M τ C (fun s => (S s).val)) ≤
        (M : ℝ)^3*(B : ℝ)^2/((T : ℝ)*Real.exp B) := by
  filter_upwards [pairRepeatEvent_probability hL hτ hτsmall] with B hB
  intro C T H M hT
  let w := siteProductMass (fun _ : Fin M => independentPrimeSetMass B)
  have hw : ∀ S, 0 ≤ w S := siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)
  calc
    _ ≤ finiteProbability w (fun S => ∃ ik : Fin M × Fin M,
        PairRepeatEvent B L T H M τ C ik.1 ik.2 (fun s => (S s).val)) := by
      apply finiteProbability_mono w hw
      intro S hS
      exact repeatedCandidateRoot_pair_event (fun i => mem_powerset.mp (S i).property) hS
    _ ≤ ∑ ik : Fin M × Fin M, finiteProbability w
        (fun S => PairRepeatEvent B L T H M τ C ik.1 ik.2 (fun s => (S s).val)) :=
      finiteProbability_union_le w hw _
    _ ≤ ∑ _ik : Fin M × Fin M, (B : ℝ)^2*(M : ℝ)/((T : ℝ)*Real.exp B) :=
      sum_le_sum (fun ik _ => hB C T H M hT ik.1 ik.2)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]; ring

end JointDickman

end OAI
