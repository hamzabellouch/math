import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ZeroObjective
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionIndex
import OAI.Combinatorics.KMedianRecovery.Sampling.ProbabilityCompEquiv

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V]

noncomputable abbrev LocalIndex (F : Finset V) (s : State V) (b : ℕ) :=
  ((V × Fin 2) ⊕ (V × Fin (Nat.clog 2 b))) ⊕ CompletionIndex F s

noncomputable abbrev LocalJoint (F : Finset V) (s : State V) (b : ℕ) :=
  ((V → Fin 4) × (V → Fin (ColorLabel.labelRange b))) × CompletionBits F s

noncomputable def localTapeEquiv (F : Finset V) (s : State V) (b : ℕ) :
    (LocalIndex F s b → Bool) ≃ LocalJoint F s b :=
  (Equiv.sumArrowEquivProdArrow _ _ Bool).trans
    (Equiv.prodCongr ((Equiv.sumArrowEquivProdArrow _ _ Bool).trans
      (Equiv.prodCongr ((Equiv.curry V (Fin 2) Bool).trans
        (Equiv.piCongrRight (fun _ => uniformBits 2)))
        ((Equiv.curry V (Fin (Nat.clog 2 b)) Bool).trans
        (Equiv.piCongrRight (fun _ => uniformBits (Nat.clog 2 b))))))
      (Equiv.refl _))

noncomputable def localTapeBound (F : Finset V) (m : ℕ) : ℕ :=
  2*Fintype.card V + Fintype.card V*m + completionTapeBound F m

omit [LinearOrder V] in
lemma localIndex_card_le (F : Finset V) (s : State V) (m b : ℕ)
    (hs : s.leaves.length ≤ m) (hb : b ≤ m) :
    Fintype.card (LocalIndex F s b) ≤ localTapeBound F m := by
  have he : Nat.clog 2 b ≤ m := Nat.clog_le_of_le_pow
    (hb.trans (Nat.le_of_lt (Nat.lt_two_pow_self (n := m))))
  have hc := completionIndex_card_le F s m hs
  have heq : Fintype.card (LocalIndex F s b) =
      Fintype.card V*2 + Fintype.card V*Nat.clog 2 b + Fintype.card (CompletionIndex F s) := by
    simp only [LocalIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  rw [heq]
  unfold localTapeBound
  nlinarith [Nat.mul_le_mul_left (Fintype.card V) he]

noncomputable def localEmbedding (F : Finset V) (s : State V) (m b : ℕ)
    (hs : s.leaves.length ≤ m) (hb : b ≤ m) : LocalIndex F s b ↪ Fin (localTapeBound F m) :=
  (Fintype.equivFin (LocalIndex F s b)).toEmbedding.trans
    ⟨Fin.castLE (localIndex_card_le F s m b hs hb),Fin.castLE_injective _⟩

noncomputable def branchJointOutput (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (b q c : ℕ) (seed : LocalJoint F s b) : Finset V := by
  classical
  letI : Nonempty V := ⟨hS.choose⟩
  exact if hb : 0 < b then
    observableOutput D F S hSF hS Δ hΔ hbound s (fun u => ColorLabel.color (seed.1.1 u))
      (fun u => ColorLabel.label b hb (seed.1.2 u)) q c seed.2
    else zeroOutput D F S hSF hS Δ hΔ hbound s (fun u => ColorLabel.color (seed.1.1 u)) q seed.2

noncomputable def branchTapeOutput (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (m b q c : ℕ) (hs : s.leaves.length ≤ m) (hb : b ≤ m)
    (tape : Fin (localTapeBound F m) → Bool) : Finset V :=
  branchJointOutput D F S hSF hS Δ hΔ hbound s b q c
    (localTapeEquiv F s b (tape ∘ localEmbedding F s m b hs hb))

omit [Fintype V] in
lemma branchJointOutput_feasible (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (b q c : ℕ) (seed : LocalJoint F s b) :
    branchJointOutput D F S hSF hS Δ hΔ hbound s b q c seed ⊆ F ∧
    (branchJointOutput D F S hSF hS Δ hΔ hbound s b q c seed).card ≤ S.card ∧
    (branchJointOutput D F S hSF hS Δ hΔ hbound s b q c seed).Nonempty := by
  classical
  let : Nonempty V := ⟨hS.choose⟩
  unfold branchJointOutput
  split_ifs with hb
  · obtain ⟨hsub,hcard,hne⟩ := observableOutput_feasible D F S hSF hS Δ hΔ hbound s
      (fun u => ColorLabel.color (seed.1.1 u))
      (fun u => ColorLabel.label b hb (seed.1.2 u)) q c seed.2
    exact ⟨hsub,hcard.le,hne⟩
  · obtain ⟨hsub,hcard,hne⟩ := zeroOutput_feasible D F S hSF hS Δ hΔ hbound s
      (fun u => ColorLabel.color (seed.1.1 u)) q seed.2
    exact ⟨hsub,hcard.le,hne⟩

lemma branchTapeOutput_feasible (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (m b q c : ℕ) (hs : s.leaves.length ≤ m) (hb : b ≤ m)
    (tape : Fin (localTapeBound F m) → Bool) :
    branchTapeOutput D F S hSF hS Δ hΔ hbound s m b q c hs hb tape ⊆ F ∧
    (branchTapeOutput D F S hSF hS Δ hΔ hbound s m b q c hs hb tape).card ≤ S.card ∧
    (branchTapeOutput D F S hSF hS Δ hΔ hbound s m b q c hs hb tape).Nonempty :=
  branchJointOutput_feasible D F S hSF hS Δ hΔ hbound s b q c _

lemma localTape_probability (F : Finset V) (s : State V) (m b : ℕ)
    (hs : s.leaves.length ≤ m) (hb : b ≤ m) (E : LocalJoint F s b → Prop) :
    probability (fun tape : Fin (localTapeBound F m) → Bool =>
      E (localTapeEquiv F s b (tape ∘ localEmbedding F s m b hs hb))) = probability E := by
  let H : (LocalIndex F s b → Bool) → Prop := fun small => E (localTapeEquiv F s b small)
  have h := probability_precompose_embedding (localEmbedding F s m b hs hb) H
  exact h.trans (probability_comp_equiv (localTapeEquiv F s b) E)

lemma branchTape_probability (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (m b q c : ℕ) (hs : s.leaves.length ≤ m) (hb : b ≤ m) (B : ℝ) :
    probability (fun tape : Fin (localTapeBound F m) → Bool =>
      realCost D (branchTapeOutput D F S hSF hS Δ hΔ hbound s m b q c hs hb tape) ≤ B) =
    probability (fun seed : LocalJoint F s b =>
      realCost D (branchJointOutput D F S hSF hS Δ hΔ hbound s b q c seed) ≤ B) := by
  exact localTape_probability F s m b hs hb
    (fun seed => realCost D (branchJointOutput D F S hSF hS Δ hΔ hbound s b q c seed) ≤ B)
end MetricKMedianRecovery.Sampling

end OAI
