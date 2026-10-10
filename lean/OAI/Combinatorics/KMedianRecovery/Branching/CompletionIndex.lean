import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionBits
import OAI.Combinatorics.KMedianRecovery.Recovery.AveragePrecomposeEmbedding

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Categorical Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable abbrev CompletionIndex (F : Finset V) (s : State V) :=
  BinaryOracleIndex (CopiedBall F (leafCenter s) (leafRadius s)) s.leaves.length
    (stepExponent s.leaves.length (19/50-1/Real.exp 1))
    (sampleCount (Fintype.card (CopiedBall F (leafCenter s) (leafRadius s)))
      s.leaves.length (19/50-1/Real.exp 1))

noncomputable def completionTapeBound (F : Finset V) (m : ℕ) : ℕ :=
  let e := stepExponent m (19/50-1/Real.exp 1)
  ((2^e*(m*F.card)*sampleCount (m*F.card) m (19/50-1/Real.exp 1)*m)+m)*e

omit [LinearOrder V] in
lemma completionIndex_card_le (F : Finset V) (s : State V) (m : ℕ)
    (hs : s.leaves.length ≤ m) : Fintype.card (CompletionIndex F s) ≤ completionTapeBound F m := by
  have hq : Fintype.card (CopiedBall F (leafCenter s) (leafRadius s)) ≤ m*F.card :=
    (Completion.copiedBall_card_le F (leafCenter s) (leafRadius s)).trans (Nat.mul_le_mul_right _ hs)
  have he := stepExponent_mono hs (19/50-1/Real.exp 1)
  have hL := sampleCount_mono hq hs (19/50-1/Real.exp 1)
  have hp : 2^stepExponent s.leaves.length (19/50-1/Real.exp 1) ≤
      (2:ℕ)^stepExponent m (19/50-1/Real.exp 1) := by gcongr
  simp only [CompletionIndex,BinaryOracleIndex,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin]
  unfold completionTapeBound
  nlinarith [Nat.mul_le_mul (Nat.mul_le_mul hp (Nat.mul_le_mul hq (Nat.mul_le_mul hL hs))) he,
    Nat.mul_le_mul hs he]

noncomputable def completionEmbedding (F : Finset V) (s : State V) (m : ℕ)
    (hs : s.leaves.length ≤ m) : CompletionIndex F s ↪ Fin (completionTapeBound F m) :=
  (Fintype.equivFin (CompletionIndex F s)).toEmbedding.trans
    ⟨Fin.castLE (completionIndex_card_le F s m hs),Fin.castLE_injective _⟩

lemma padded_completion_probability (F : Finset V) (s : State V) (m : ℕ)
    (hs : s.leaves.length ≤ m) (E : CompletionBits F s → Prop) :
    FiniteSampling.probability (fun bits : Fin (completionTapeBound F m) → Bool =>
      E (bits ∘ completionEmbedding F s m hs)) = FiniteSampling.probability E :=
  FiniteSampling.probability_precompose_embedding (completionEmbedding F s m hs) E
end MetricKMedianRecovery.Sampling

end OAI
