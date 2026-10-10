import OAI.NumberTheory.JointDickman.Amplification.CandidateRepeatEvent
import OAI.NumberTheory.JointDickman.Amplification.FiniteEventUnion

namespace OAI

/-! # Conditional union over all candidates of an exposed endpoint pair -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

/-- There are at most B squared local candidates after both endpoints
are exposed, so their third-site probabilities remain negligible. -/
theorem pairRepeatEvent_conditional_bound {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), 0 < T → ∀ (i k : Fin M),
      ∀ a : ({i,k} : Finset (Fin M)) → (auxiliaryPrimes B).powerset,
      finiteProbability (siteProductMass
        (fun _ : {s : Fin M // s ∉ ({i,k} : Finset (Fin M))} => independentPrimeSetMass B))
        (fun b => PairRepeatEvent B L T H M τ C i k
          (fun s => (mergeSitePartition {i,k} a b s).val)) ≤
        (B : ℝ)^2*(M : ℝ)/((T : ℝ)*Real.exp B) := by
  classical
  filter_upwards [endpointSplits_card hL hτ hτsmall] with B hcard
  intro C T H M hT i k a
  let I : Finset (Fin M) := {i,k}
  let S₁ := (a ⟨i,by simp⟩).val
  let S₂ := (a ⟨k,by simp⟩).val
  let J := pairSplitChoices B L τ C S₁ S₂
  let w := siteProductMass (fun _ : {s : Fin M // s ∉ I} => independentPrimeSetMass B)
  let Z := (M : ℝ)/((T : ℝ)*Real.exp B)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hJ : (J.card : ℝ) ≤ (B : ℝ)^2 := by
    have hn : J.card ≤ B*B := by
      dsimp [J,pairSplitChoices]
      rw [card_product]
      exact Nat.mul_le_mul (hcard C S₁) (hcard C S₂)
    simpa only [pow_two] using (show (J.card : ℝ) ≤ (B : ℝ)*B by exact_mod_cast hn)
  have hmerge₁ (b : {s : Fin M // s ∉ I} → (auxiliaryPrimes B).powerset) :
      (mergeSitePartition I a b i).val = S₁ := by simp [mergeSitePartition,I,S₁]
  have hmerge₂ (b : {s : Fin M // s ∉ I} → (auxiliaryPrimes B).powerset) :
      (mergeSitePartition I a b k).val = S₂ := by simp [mergeSitePartition,I,S₂]
  let E := fun (ab : Finset ℕ × Finset ℕ) (b : {s : Fin M // s ∉ I} → (auxiliaryPrimes B).powerset) =>
    BlockCandidateAdmissible B L T H τ C ((i,k),ab) ∧
      CandidateRepeatWitness T ((i,k),ab) (fun s => (mergeSitePartition I a b s).val)
  have hprob (ab : Finset ℕ × Finset ℕ) : finiteProbability w (E ab) ≤ Z := by
    by_cases he : BlockCandidateAdmissible B L T H τ C ((i,k),ab)
    · simpa only [E,he,true_and] using repeatWitness_remaining_probability hT he a
    · simpa only [E,he,false_and,finiteProbability,ite_false,sum_const_zero] using hZ
  have hevent : (fun b => PairRepeatEvent B L T H M τ C i k
      (fun s => (mergeSitePartition I a b s).val)) = (fun b => ∃ ab ∈ J, E ab b) := by
    funext b
    simp only [PairRepeatEvent,hmerge₁,hmerge₂,J,E]
  rw [hevent]
  calc
    _ ≤ ∑ ab ∈ J, finiteProbability w (E ab) := finiteProbability_exists_mem w
      (siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)) J E
    _ ≤ ∑ _ab ∈ J, Z := sum_le_sum (fun ab _ => hprob ab)
    _ = (J.card : ℝ)*Z := by simp
    _ ≤ (B : ℝ)^2*Z := mul_le_mul_of_nonneg_right hJ hZ
    _ = _ := by dsimp [Z]; ring

end JointDickman

end OAI
